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
uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1862_ = 1;
v___x_1863_ = lean_array_uget_borrowed(v_as_1858_, v_i_1859_);
v___x_1864_ = l_Lean_Expr_fvarId_x21(v___x_1863_);
v___x_1865_ = l_Lean_instBEqFVarId_beq(v___x_1864_, v_fvarId_1856_);
lean_dec(v___x_1864_);
if (v___x_1865_ == 0)
{
if (v___x_1857_ == 0)
{
size_t v___x_1866_; size_t v___x_1867_; 
v___x_1866_ = ((size_t)1ULL);
v___x_1867_ = lean_usize_add(v_i_1859_, v___x_1866_);
v_i_1859_ = v___x_1867_;
goto _start;
}
else
{
return v___x_1862_;
}
}
else
{
return v___x_1862_;
}
}
else
{
uint8_t v___x_1869_; 
v___x_1869_ = 0;
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1870_, lean_object* v___x_1871_, lean_object* v_as_1872_, lean_object* v_i_1873_, lean_object* v_stop_1874_){
_start:
{
uint8_t v___x_7581__boxed_1875_; size_t v_i_boxed_1876_; size_t v_stop_boxed_1877_; uint8_t v_res_1878_; lean_object* v_r_1879_; 
v___x_7581__boxed_1875_ = lean_unbox(v___x_1871_);
v_i_boxed_1876_ = lean_unbox_usize(v_i_1873_);
lean_dec(v_i_1873_);
v_stop_boxed_1877_ = lean_unbox_usize(v_stop_1874_);
lean_dec(v_stop_1874_);
v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1870_, v___x_7581__boxed_1875_, v_as_1872_, v_i_boxed_1876_, v_stop_boxed_1877_);
lean_dec_ref(v_as_1872_);
lean_dec(v_fvarId_1870_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1880_, lean_object* v___x_1881_, uint8_t v___x_1882_, lean_object* v___x_1883_, lean_object* v_fvarId_1884_){
_start:
{
uint8_t v___x_1885_; lean_object* v___y_1887_; 
v___x_1885_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
if (v___x_1885_ == 0)
{
uint8_t v___x_1892_; 
lean_dec(v___x_1881_);
v___x_1892_ = 1;
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_get_size(v___x_1883_);
v___x_1894_ = lean_nat_dec_le(v___x_1881_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec(v___x_1881_);
v___y_1887_ = v___x_1893_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v___x_1881_;
goto v___jp_1886_;
}
}
v___jp_1886_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_lt(v___x_1880_, v___y_1887_);
if (v___x_1888_ == 0)
{
lean_dec(v___y_1887_);
return v___x_1885_;
}
else
{
size_t v___x_1889_; size_t v___x_1890_; uint8_t v___x_1891_; 
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___y_1887_);
lean_dec(v___y_1887_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1884_, v___x_1882_, v___x_1883_, v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
return v___x_1888_;
}
else
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v_fvarId_1899_){
_start:
{
uint8_t v___x_7604__boxed_1900_; uint8_t v_res_1901_; lean_object* v_r_1902_; 
v___x_7604__boxed_1900_ = lean_unbox(v___x_1897_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1895_, v___x_1896_, v___x_7604__boxed_1900_, v___x_1898_, v_fvarId_1899_);
lean_dec(v_fvarId_1899_);
lean_dec_ref(v___x_1898_);
lean_dec(v___x_1895_);
v_r_1902_ = lean_box(v_res_1901_);
return v_r_1902_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1903_, lean_object* v_as_1904_, size_t v_i_1905_, size_t v_stop_1906_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_usize_dec_eq(v_i_1905_, v_stop_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_array_uget_borrowed(v_as_1904_, v_i_1905_);
v___x_1909_ = l_Lean_Expr_fvarId_x21(v___x_1908_);
v___x_1910_ = l_Lean_instBEqFVarId_beq(v___x_1903_, v___x_1909_);
lean_dec(v___x_1909_);
if (v___x_1910_ == 0)
{
size_t v___x_1911_; size_t v___x_1912_; 
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1905_, v___x_1911_);
v_i_1905_ = v___x_1912_;
goto _start;
}
else
{
return v___x_1910_;
}
}
else
{
uint8_t v___x_1914_; 
v___x_1914_ = 0;
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1915_, lean_object* v_as_1916_, lean_object* v_i_1917_, lean_object* v_stop_1918_){
_start:
{
size_t v_i_boxed_1919_; size_t v_stop_boxed_1920_; uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_i_boxed_1919_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_stop_boxed_1920_ = lean_unbox_usize(v_stop_1918_);
lean_dec(v_stop_1918_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1915_, v_as_1916_, v_i_boxed_1919_, v_stop_boxed_1920_);
lean_dec_ref(v_as_1916_);
lean_dec(v___x_1915_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1923_, lean_object* v_x_1924_){
_start:
{
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1925_, lean_object* v_x_1926_){
_start:
{
uint8_t v___x_7653__boxed_1927_; uint8_t v_res_1928_; lean_object* v_r_1929_; 
v___x_7653__boxed_1927_ = lean_unbox(v___x_1925_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7653__boxed_1927_, v_x_1926_);
lean_dec(v_x_1926_);
v_r_1929_ = lean_box(v_res_1928_);
return v_r_1929_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_unsigned_to_nat(16u);
v___x_1932_ = lean_mk_array(v___x_1931_, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1936_, lean_object* v___x_1937_, lean_object* v___x_1938_, lean_object* v_ctx_1939_, lean_object* v_as_1940_, size_t v_i_1941_, size_t v_stop_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_eq(v_i_1941_, v_stop_1942_);
if (v___x_1945_ == 0)
{
uint8_t v___x_1946_; uint8_t v_a_1948_; uint8_t v_a_1955_; uint8_t v_fst_1959_; lean_object* v_mctx_1960_; lean_object* v___y_1976_; uint8_t v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___y_2000_; uint8_t v_fst_2005_; lean_object* v_mctx_2006_; lean_object* v___y_2022_; lean_object* v___x_2027_; 
v___x_1946_ = 1;
v___x_2027_ = lean_array_uget_borrowed(v_as_1940_, v_i_1941_);
if (lean_obj_tag(v___x_2027_) == 0)
{
v_a_1948_ = v___x_1936_;
goto v___jp_1947_;
}
else
{
lean_object* v_val_2028_; lean_object* v_majorDecl_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_val_2028_ = lean_ctor_get(v___x_2027_, 0);
v_majorDecl_2029_ = lean_ctor_get(v_ctx_1939_, 2);
v___x_2030_ = l_Lean_LocalDecl_fvarId(v_val_2028_);
v___x_2031_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2029_);
v___x_2032_ = l_Lean_instBEqFVarId_beq(v___x_2030_, v___x_2031_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___f_2037_; lean_object* v___y_2039_; lean_object* v_snd_2040_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2084_; uint8_t v___x_2089_; 
v___x_2033_ = lean_box(v___x_1936_);
v___f_2034_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2034_, 0, v___x_2033_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_box(v___x_1936_);
lean_inc_ref(v___x_1937_);
lean_inc(v___x_1938_);
v___f_2037_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2037_, 0, v___x_2035_);
lean_closure_set(v___f_2037_, 1, v___x_1938_);
lean_closure_set(v___f_2037_, 2, v___x_2036_);
lean_closure_set(v___f_2037_, 3, v___x_1937_);
v___x_2089_ = lean_nat_dec_lt(v___x_2035_, v___x_1938_);
if (v___x_2089_ == 0)
{
lean_dec(v___x_2030_);
goto v___jp_2053_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_array_get_size(v___x_1937_);
v___x_2091_ = lean_nat_dec_le(v___x_1938_, v___x_2090_);
if (v___x_2091_ == 0)
{
v___y_2084_ = v___x_2090_;
goto v___jp_2083_;
}
else
{
lean_inc(v___x_1938_);
v___y_2084_ = v___x_1938_;
goto v___jp_2083_;
}
}
v___jp_2038_:
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_hasFVar(v___y_2039_);
if (v___x_2041_ == 0)
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_hasMVar(v___y_2039_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v___y_2039_);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v___f_2034_);
v_fst_1982_ = v___x_2042_;
v_snd_1983_ = v_snd_2040_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v___y_2039_, v_snd_2040_);
v___y_2000_ = v___x_2043_;
goto v___jp_1999_;
}
}
else
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v___y_2039_, v_snd_2040_);
v___y_2000_ = v___x_2044_;
goto v___jp_1999_;
}
}
v___jp_2045_:
{
lean_object* v_fst_2048_; uint8_t v___x_2049_; 
v_fst_2048_ = lean_ctor_get(v___y_2047_, 0);
v___x_2049_ = lean_unbox(v_fst_2048_);
if (v___x_2049_ == 0)
{
lean_object* v_snd_2050_; 
v_snd_2050_ = lean_ctor_get(v___y_2047_, 1);
lean_inc(v_snd_2050_);
lean_dec_ref(v___y_2047_);
v___y_2039_ = v___y_2046_;
v_snd_2040_ = v_snd_2050_;
goto v___jp_2038_;
}
else
{
lean_object* v_snd_2051_; uint8_t v___x_2052_; 
lean_inc(v_fst_2048_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v___f_2034_);
v_snd_2051_ = lean_ctor_get(v___y_2047_, 1);
lean_inc(v_snd_2051_);
lean_dec_ref(v___y_2047_);
v___x_2052_ = lean_unbox(v_fst_2048_);
lean_dec(v_fst_2048_);
v_fst_1982_ = v___x_2052_;
v_snd_1983_ = v_snd_2051_;
goto v___jp_1981_;
}
}
v___jp_2053_:
{
if (lean_obj_tag(v_val_2028_) == 0)
{
lean_object* v_type_2054_; lean_object* v___x_2055_; lean_object* v_mctx_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_type_2054_ = lean_ctor_get(v_val_2028_, 3);
v___x_2055_ = lean_st_ref_get(v___y_1943_);
v_mctx_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_ref_n(v_mctx_2056_, 2);
lean_dec(v___x_2055_);
v___x_2057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_mctx_2056_);
v___x_2059_ = l_Lean_Expr_hasFVar(v_type_2054_);
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Expr_hasMVar(v_type_2054_);
if (v___x_2060_ == 0)
{
lean_dec_ref_known(v___x_2058_, 2);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v___f_2034_);
v_fst_2005_ = v___x_2060_;
v_mctx_2006_ = v_mctx_2056_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v_mctx_2056_);
lean_inc_ref(v_type_2054_);
v___x_2061_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2054_, v___x_2058_);
v___y_2022_ = v___x_2061_;
goto v___jp_2021_;
}
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref(v_mctx_2056_);
lean_inc_ref(v_type_2054_);
v___x_2062_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2054_, v___x_2058_);
v___y_2022_ = v___x_2062_;
goto v___jp_2021_;
}
}
else
{
uint8_t v_nondep_2063_; 
v_nondep_2063_ = lean_ctor_get_uint8(v_val_2028_, sizeof(void*)*5);
if (v_nondep_2063_ == 0)
{
lean_object* v_type_2064_; lean_object* v_value_2065_; lean_object* v___x_2066_; lean_object* v_mctx_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_type_2064_ = lean_ctor_get(v_val_2028_, 3);
v_value_2065_ = lean_ctor_get(v_val_2028_, 4);
v___x_2066_ = lean_st_ref_get(v___y_1943_);
v_mctx_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_ref(v_mctx_2067_);
lean_dec(v___x_2066_);
v___x_2068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_mctx_2067_);
v___x_2070_ = l_Lean_Expr_hasFVar(v_type_2064_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = l_Lean_Expr_hasMVar(v_type_2064_);
if (v___x_2071_ == 0)
{
lean_inc_ref(v_value_2065_);
v___y_2039_ = v_value_2065_;
v_snd_2040_ = v___x_2069_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2072_; 
lean_inc_ref(v_type_2064_);
lean_inc_ref(v___f_2034_);
lean_inc_ref(v___f_2037_);
v___x_2072_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2064_, v___x_2069_);
lean_inc_ref(v_value_2065_);
v___y_2046_ = v_value_2065_;
v___y_2047_ = v___x_2072_;
goto v___jp_2045_;
}
}
else
{
lean_object* v___x_2073_; 
lean_inc_ref(v_type_2064_);
lean_inc_ref(v___f_2034_);
lean_inc_ref(v___f_2037_);
v___x_2073_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2064_, v___x_2069_);
lean_inc_ref(v_value_2065_);
v___y_2046_ = v_value_2065_;
v___y_2047_ = v___x_2073_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_type_2074_; lean_object* v___x_2075_; lean_object* v_mctx_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_type_2074_ = lean_ctor_get(v_val_2028_, 3);
v___x_2075_ = lean_st_ref_get(v___y_1943_);
v_mctx_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_ref_n(v_mctx_2076_, 2);
lean_dec(v___x_2075_);
v___x_2077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v_mctx_2076_);
v___x_2079_ = l_Lean_Expr_hasFVar(v_type_2074_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
v___x_2080_ = l_Lean_Expr_hasMVar(v_type_2074_);
if (v___x_2080_ == 0)
{
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v___f_2037_);
lean_dec_ref(v___f_2034_);
v_fst_1959_ = v___x_2080_;
v_mctx_1960_ = v_mctx_2076_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v_mctx_2076_);
lean_inc_ref(v_type_2074_);
v___x_2081_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2074_, v___x_2078_);
v___y_1976_ = v___x_2081_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec_ref(v_mctx_2076_);
lean_inc_ref(v_type_2074_);
v___x_2082_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2037_, v___f_2034_, v_type_2074_, v___x_2078_);
v___y_1976_ = v___x_2082_;
goto v___jp_1975_;
}
}
}
}
v___jp_2083_:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_nat_dec_lt(v___x_2035_, v___y_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v___y_2084_);
lean_dec(v___x_2030_);
goto v___jp_2053_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; uint8_t v___x_2088_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___y_2084_);
lean_dec(v___y_2084_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2030_, v___x_1937_, v___x_2086_, v___x_2087_);
lean_dec(v___x_2030_);
if (v___x_2088_ == 0)
{
goto v___jp_2053_;
}
else
{
lean_dec_ref(v___f_2037_);
lean_dec_ref(v___f_2034_);
v_a_1948_ = v___x_1936_;
goto v___jp_1947_;
}
}
}
}
else
{
lean_dec(v___x_2030_);
v_a_1948_ = v___x_1936_;
goto v___jp_1947_;
}
}
v___jp_1947_:
{
if (v_a_1948_ == 0)
{
size_t v___x_1949_; size_t v___x_1950_; 
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1941_, v___x_1949_);
v_i_1941_ = v___x_1950_;
goto _start;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v___x_1938_);
lean_dec_ref(v___x_1937_);
v___x_1952_ = lean_box(v___x_1946_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
v___jp_1954_:
{
if (v_a_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v___x_1938_);
lean_dec_ref(v___x_1937_);
v___x_1956_ = lean_box(v___x_1946_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
else
{
v_a_1948_ = v___x_1936_;
goto v___jp_1947_;
}
}
v___jp_1958_:
{
lean_object* v___x_1961_; lean_object* v_cache_1962_; lean_object* v_zetaDeltaFVarIds_1963_; lean_object* v_postponed_1964_; lean_object* v_diag_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v___x_1961_ = lean_st_ref_take(v___y_1943_);
v_cache_1962_ = lean_ctor_get(v___x_1961_, 1);
v_zetaDeltaFVarIds_1963_ = lean_ctor_get(v___x_1961_, 2);
v_postponed_1964_ = lean_ctor_get(v___x_1961_, 3);
v_diag_1965_ = lean_ctor_get(v___x_1961_, 4);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1961_, 0);
lean_dec(v_unused_1974_);
v___x_1967_ = v___x_1961_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_diag_1965_);
lean_inc(v_postponed_1964_);
lean_inc(v_zetaDeltaFVarIds_1963_);
lean_inc(v_cache_1962_);
lean_dec(v___x_1961_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_mctx_1960_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_mctx_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_cache_1962_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_zetaDeltaFVarIds_1963_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_postponed_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_diag_1965_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_st_ref_put(v___y_1943_, v___x_1970_);
v_a_1955_ = v_fst_1959_;
goto v___jp_1954_;
}
}
}
v___jp_1975_:
{
lean_object* v_snd_1977_; lean_object* v_fst_1978_; lean_object* v_mctx_1979_; uint8_t v___x_1980_; 
v_snd_1977_ = lean_ctor_get(v___y_1976_, 1);
lean_inc(v_snd_1977_);
v_fst_1978_ = lean_ctor_get(v___y_1976_, 0);
lean_inc(v_fst_1978_);
lean_dec_ref(v___y_1976_);
v_mctx_1979_ = lean_ctor_get(v_snd_1977_, 1);
lean_inc_ref(v_mctx_1979_);
lean_dec(v_snd_1977_);
v___x_1980_ = lean_unbox(v_fst_1978_);
lean_dec(v_fst_1978_);
v_fst_1959_ = v___x_1980_;
v_mctx_1960_ = v_mctx_1979_;
goto v___jp_1958_;
}
v___jp_1981_:
{
lean_object* v_mctx_1984_; lean_object* v___x_1985_; lean_object* v_cache_1986_; lean_object* v_zetaDeltaFVarIds_1987_; lean_object* v_postponed_1988_; lean_object* v_diag_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1997_; 
v_mctx_1984_ = lean_ctor_get(v_snd_1983_, 1);
lean_inc_ref(v_mctx_1984_);
lean_dec_ref(v_snd_1983_);
v___x_1985_ = lean_st_ref_take(v___y_1943_);
v_cache_1986_ = lean_ctor_get(v___x_1985_, 1);
v_zetaDeltaFVarIds_1987_ = lean_ctor_get(v___x_1985_, 2);
v_postponed_1988_ = lean_ctor_get(v___x_1985_, 3);
v_diag_1989_ = lean_ctor_get(v___x_1985_, 4);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1985_, 0);
lean_dec(v_unused_1998_);
v___x_1991_ = v___x_1985_;
v_isShared_1992_ = v_isSharedCheck_1997_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_diag_1989_);
lean_inc(v_postponed_1988_);
lean_inc(v_zetaDeltaFVarIds_1987_);
lean_inc(v_cache_1986_);
lean_dec(v___x_1985_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1997_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v_mctx_1984_);
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_mctx_1984_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_cache_1986_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_zetaDeltaFVarIds_1987_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_postponed_1988_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_diag_1989_);
v___x_1994_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_st_ref_put(v___y_1943_, v___x_1994_);
v_a_1955_ = v_fst_1982_;
goto v___jp_1954_;
}
}
}
v___jp_1999_:
{
lean_object* v_fst_2001_; lean_object* v_snd_2002_; uint8_t v___x_2003_; 
v_fst_2001_ = lean_ctor_get(v___y_2000_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v___y_2000_, 1);
lean_inc(v_snd_2002_);
lean_dec_ref(v___y_2000_);
v___x_2003_ = lean_unbox(v_fst_2001_);
lean_dec(v_fst_2001_);
v_fst_1982_ = v___x_2003_;
v_snd_1983_ = v_snd_2002_;
goto v___jp_1981_;
}
v___jp_2004_:
{
lean_object* v___x_2007_; lean_object* v_cache_2008_; lean_object* v_zetaDeltaFVarIds_2009_; lean_object* v_postponed_2010_; lean_object* v_diag_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v___x_2007_ = lean_st_ref_take(v___y_1943_);
v_cache_2008_ = lean_ctor_get(v___x_2007_, 1);
v_zetaDeltaFVarIds_2009_ = lean_ctor_get(v___x_2007_, 2);
v_postponed_2010_ = lean_ctor_get(v___x_2007_, 3);
v_diag_2011_ = lean_ctor_get(v___x_2007_, 4);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2020_);
v___x_2013_ = v___x_2007_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_diag_2011_);
lean_inc(v_postponed_2010_);
lean_inc(v_zetaDeltaFVarIds_2009_);
lean_inc(v_cache_2008_);
lean_dec(v___x_2007_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v_mctx_2006_);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_mctx_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_cache_2008_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_zetaDeltaFVarIds_2009_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_postponed_2010_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_diag_2011_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_st_ref_put(v___y_1943_, v___x_2016_);
v_a_1955_ = v_fst_2005_;
goto v___jp_1954_;
}
}
}
v___jp_2021_:
{
lean_object* v_snd_2023_; lean_object* v_fst_2024_; lean_object* v_mctx_2025_; uint8_t v___x_2026_; 
v_snd_2023_ = lean_ctor_get(v___y_2022_, 1);
lean_inc(v_snd_2023_);
v_fst_2024_ = lean_ctor_get(v___y_2022_, 0);
lean_inc(v_fst_2024_);
lean_dec_ref(v___y_2022_);
v_mctx_2025_ = lean_ctor_get(v_snd_2023_, 1);
lean_inc_ref(v_mctx_2025_);
lean_dec(v_snd_2023_);
v___x_2026_ = lean_unbox(v_fst_2024_);
lean_dec(v_fst_2024_);
v_fst_2005_ = v___x_2026_;
v_mctx_2006_ = v_mctx_2025_;
goto v___jp_2004_;
}
}
else
{
uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v___x_1938_);
lean_dec_ref(v___x_1937_);
v___x_2092_ = 0;
v___x_2093_ = lean_box(v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v_ctx_2098_, lean_object* v_as_2099_, lean_object* v_i_2100_, lean_object* v_stop_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_7683__boxed_2104_; size_t v_i_boxed_2105_; size_t v_stop_boxed_2106_; lean_object* v_res_2107_; 
v___x_7683__boxed_2104_ = lean_unbox(v___x_2095_);
v_i_boxed_2105_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_stop_boxed_2106_ = lean_unbox_usize(v_stop_2101_);
lean_dec(v_stop_2101_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7683__boxed_2104_, v___x_2096_, v___x_2097_, v_ctx_2098_, v_as_2099_, v_i_boxed_2105_, v_stop_boxed_2106_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v_as_2099_);
lean_dec_ref(v_ctx_2098_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2108_, lean_object* v___x_2109_, lean_object* v___x_2110_, lean_object* v_ctx_2111_, lean_object* v_x_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v_cs_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2132_; 
v_cs_2118_ = lean_ctor_get(v_x_2112_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2112_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2120_ = v_x_2112_;
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_cs_2118_);
lean_dec(v_x_2112_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_array_get_size(v_cs_2118_);
v___x_2124_ = lean_nat_dec_lt(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec_ref(v_cs_2118_);
lean_dec(v___x_2110_);
lean_dec_ref(v___x_2109_);
v___x_2125_ = lean_box(v___x_2124_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2125_);
v___x_2127_ = v___x_2120_;
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
lean_del_object(v___x_2120_);
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = lean_usize_of_nat(v___x_2123_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2108_, v___x_2109_, v___x_2110_, v_ctx_2111_, v_cs_2118_, v___x_2129_, v___x_2130_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v_cs_2118_);
return v___x_2131_;
}
}
}
else
{
lean_object* v_vs_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_vs_2133_ = lean_ctor_get(v_x_2112_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2112_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2135_ = v_x_2112_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_vs_2133_);
lean_dec(v_x_2112_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
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
lean_dec(v___x_2110_);
lean_dec_ref(v___x_2109_);
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
size_t v___x_2144_; size_t v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2135_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = lean_usize_of_nat(v___x_2138_);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2108_, v___x_2109_, v___x_2110_, v_ctx_2111_, v_vs_2133_, v___x_2144_, v___x_2145_, v___y_2114_);
lean_dec_ref(v_vs_2133_);
return v___x_2146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_ctx_2151_, lean_object* v_as_2152_, size_t v_i_2153_, size_t v_stop_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_usize_dec_eq(v_i_2153_, v_stop_2154_);
if (v___x_2160_ == 0)
{
uint8_t v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = 1;
v___x_2162_ = lean_array_uget_borrowed(v_as_2152_, v_i_2153_);
lean_inc(v___x_2162_);
lean_inc(v___x_2150_);
lean_inc_ref(v___x_2149_);
v___x_2163_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2148_, v___x_2149_, v___x_2150_, v_ctx_2151_, v___x_2162_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2176_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
if (v___x_2168_ == 0)
{
size_t v___x_2169_; size_t v___x_2170_; 
lean_del_object(v___x_2166_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2153_, v___x_2169_);
v_i_2153_ = v___x_2170_;
goto _start;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v___x_2150_);
lean_dec_ref(v___x_2149_);
v___x_2172_ = lean_box(v___x_2161_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2172_);
v___x_2174_ = v___x_2166_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_dec(v___x_2150_);
lean_dec_ref(v___x_2149_);
return v___x_2163_;
}
}
else
{
uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec(v___x_2150_);
lean_dec_ref(v___x_2149_);
v___x_2177_ = 0;
v___x_2178_ = lean_box(v___x_2177_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v___x_2182_, lean_object* v_ctx_2183_, lean_object* v_as_2184_, lean_object* v_i_2185_, lean_object* v_stop_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v___x_7980__boxed_2192_; size_t v_i_boxed_2193_; size_t v_stop_boxed_2194_; lean_object* v_res_2195_; 
v___x_7980__boxed_2192_ = lean_unbox(v___x_2180_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_stop_boxed_2194_ = lean_unbox_usize(v_stop_2186_);
lean_dec(v_stop_2186_);
v_res_2195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7980__boxed_2192_, v___x_2181_, v___x_2182_, v_ctx_2183_, v_as_2184_, v_i_boxed_2193_, v_stop_boxed_2194_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_as_2184_);
lean_dec_ref(v_ctx_2183_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v___x_2198_, lean_object* v_ctx_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_8000__boxed_2206_; lean_object* v_res_2207_; 
v___x_8000__boxed_2206_ = lean_unbox(v___x_2196_);
v_res_2207_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_8000__boxed_2206_, v___x_2197_, v___x_2198_, v_ctx_2199_, v_x_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_ctx_2199_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2208_, lean_object* v___x_2209_, lean_object* v___x_2210_, lean_object* v_ctx_2211_, lean_object* v_t_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_root_2218_; lean_object* v_tail_2219_; lean_object* v___x_2220_; 
v_root_2218_ = lean_ctor_get(v_t_2212_, 0);
lean_inc_ref(v_root_2218_);
v_tail_2219_ = lean_ctor_get(v_t_2212_, 1);
lean_inc_ref(v_tail_2219_);
lean_dec_ref(v_t_2212_);
lean_inc(v___x_2210_);
lean_inc_ref(v___x_2209_);
v___x_2220_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2208_, v___x_2209_, v___x_2210_, v_ctx_2211_, v_root_2218_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; uint8_t v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v___x_2222_ = lean_unbox(v_a_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2236_; 
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2237_);
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2236_;
goto v_resetjp_2223_;
}
else
{
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2236_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v_tail_2219_);
v___x_2228_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_dec_ref(v_tail_2219_);
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2209_);
v___x_2229_ = lean_box(v___x_2228_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
size_t v___x_2233_; size_t v___x_2234_; lean_object* v___x_2235_; 
lean_del_object(v___x_2224_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = lean_usize_of_nat(v___x_2227_);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2208_, v___x_2209_, v___x_2210_, v_ctx_2211_, v_tail_2219_, v___x_2233_, v___x_2234_, v___y_2214_);
lean_dec_ref(v_tail_2219_);
return v___x_2235_;
}
}
}
else
{
lean_dec_ref(v_tail_2219_);
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2209_);
return v___x_2220_;
}
}
else
{
lean_dec_ref(v_tail_2219_);
lean_dec(v___x_2210_);
lean_dec_ref(v___x_2209_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v_ctx_2241_, lean_object* v_t_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v___x_8132__boxed_2248_; lean_object* v_res_2249_; 
v___x_8132__boxed_2248_ = lean_unbox(v___x_2238_);
v_res_2249_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8132__boxed_2248_, v___x_2239_, v___x_2240_, v_ctx_2241_, v_t_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v_ctx_2241_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_majorTypeIndices_2256_; lean_object* v___x_2257_; uint8_t v___y_2259_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_majorTypeIndices_2256_ = lean_ctor_get(v_ctx_2250_, 5);
lean_inc_ref(v_majorTypeIndices_2256_);
v___x_2257_ = lean_array_get_size(v_majorTypeIndices_2256_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_nat_dec_eq(v___x_2257_, v___x_2281_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_lt(v___x_2281_, v___x_2257_);
if (v___x_2283_ == 0)
{
v___y_2259_ = v___x_2283_;
goto v___jp_2258_;
}
else
{
if (v___x_2283_ == 0)
{
v___y_2259_ = v___x_2283_;
goto v___jp_2258_;
}
else
{
size_t v___x_2284_; size_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = lean_usize_of_nat(v___x_2257_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2257_, v_majorTypeIndices_2256_, v___x_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
v___y_2259_ = v___x_2286_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_majorTypeIndices_2256_);
lean_dec_ref(v_ctx_2250_);
v___x_2287_ = lean_box(v___x_2282_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v_majorTypeIndices_2256_);
lean_dec_ref(v_ctx_2250_);
v___x_2289_ = lean_box(v___x_2282_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
v___jp_2258_:
{
uint8_t v___x_2260_; 
v___x_2260_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2256_, v___x_2257_, v___x_2257_);
if (v___x_2260_ == 0)
{
lean_object* v_lctx_2261_; lean_object* v_decls_2262_; lean_object* v___x_2263_; 
v_lctx_2261_ = lean_ctor_get(v_a_2251_, 2);
v_decls_2262_ = lean_ctor_get(v_lctx_2261_, 1);
lean_inc_ref(v_decls_2262_);
v___x_2263_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2260_, v_majorTypeIndices_2256_, v___x_2257_, v_ctx_2250_, v_decls_2262_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec_ref(v_ctx_2250_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2278_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2278_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2278_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_unbox(v_a_2264_);
lean_dec(v_a_2264_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2269_ = 1;
v___x_2270_ = lean_box(v___x_2269_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2270_);
v___x_2272_ = v___x_2266_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(v___x_2260_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2274_);
v___x_2276_ = v___x_2266_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
return v___x_2263_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v_majorTypeIndices_2256_);
lean_dec_ref(v_ctx_2250_);
v___x_2279_ = lean_box(v___y_2259_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2298_, lean_object* v_i_2299_, lean_object* v_n_2300_, lean_object* v_i_2301_, lean_object* v_a_2302_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2298_, v_i_2299_, v_n_2300_, v_i_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2304_, lean_object* v_i_2305_, lean_object* v_n_2306_, lean_object* v_i_2307_, lean_object* v_a_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2304_, v_i_2305_, v_n_2306_, v_i_2307_, v_a_2308_);
lean_dec(v_n_2306_);
lean_dec(v_i_2305_);
lean_dec_ref(v___x_2304_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2311_, lean_object* v_n_2312_, lean_object* v_i_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2311_, v_n_2312_, v_i_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2316_, lean_object* v_n_2317_, lean_object* v_i_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v_res_2320_; lean_object* v_r_2321_; 
v_res_2320_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2316_, v_n_2317_, v_i_2318_, v_a_2319_);
lean_dec(v_n_2317_);
lean_dec_ref(v___x_2316_);
v_r_2321_ = lean_box(v_res_2320_);
return v_r_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2322_, lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v_ctx_2325_, lean_object* v_as_2326_, size_t v_i_2327_, size_t v_stop_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2322_, v___x_2323_, v___x_2324_, v_ctx_2325_, v_as_2326_, v_i_2327_, v_stop_2328_, v___y_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v___x_2337_, lean_object* v_ctx_2338_, lean_object* v_as_2339_, lean_object* v_i_2340_, lean_object* v_stop_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v___x_8277__boxed_2347_; size_t v_i_boxed_2348_; size_t v_stop_boxed_2349_; lean_object* v_res_2350_; 
v___x_8277__boxed_2347_ = lean_unbox(v___x_2335_);
v_i_boxed_2348_ = lean_unbox_usize(v_i_2340_);
lean_dec(v_i_2340_);
v_stop_boxed_2349_ = lean_unbox_usize(v_stop_2341_);
lean_dec(v_stop_2341_);
v_res_2350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8277__boxed_2347_, v___x_2336_, v___x_2337_, v_ctx_2338_, v_as_2339_, v_i_boxed_2348_, v_stop_boxed_2349_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v_as_2339_);
lean_dec_ref(v_ctx_2338_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2351_, size_t v_i_2352_, size_t v_stop_2353_, lean_object* v_b_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_a_2361_; uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_eq(v_i_2352_, v_stop_2353_);
if (v___x_2365_ == 0)
{
lean_object* v_toInductionSubgoal_2366_; lean_object* v_ctorName_2367_; lean_object* v_mvarId_2368_; lean_object* v_fields_2369_; lean_object* v_subst_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2421_; 
v_toInductionSubgoal_2366_ = lean_ctor_get(v_b_2354_, 0);
lean_inc_ref(v_toInductionSubgoal_2366_);
v_ctorName_2367_ = lean_ctor_get(v_b_2354_, 1);
v_mvarId_2368_ = lean_ctor_get(v_toInductionSubgoal_2366_, 0);
v_fields_2369_ = lean_ctor_get(v_toInductionSubgoal_2366_, 1);
v_subst_2370_ = lean_ctor_get(v_toInductionSubgoal_2366_, 2);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_toInductionSubgoal_2366_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2372_ = v_toInductionSubgoal_2366_;
v_isShared_2373_ = v_isSharedCheck_2421_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_subst_2370_);
lean_inc(v_fields_2369_);
lean_inc(v_mvarId_2368_);
lean_dec(v_toInductionSubgoal_2366_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2421_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_array_uget_borrowed(v_as_2351_, v_i_2352_);
lean_inc(v___x_2374_);
v___x_2375_ = l_Lean_Meta_FVarSubst_get(v_subst_2370_, v___x_2374_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v_fvarId_2376_; lean_object* v___x_2377_; 
v_fvarId_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_fvarId_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l_Lean_Meta_saveState___redArg(v___y_2356_, v___y_2358_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = l_Lean_MVarId_clear(v_mvarId_2368_, v_fvarId_2376_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2391_; 
lean_inc(v_ctorName_2367_);
lean_dec(v_a_2378_);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_b_2354_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; lean_object* v_unused_2393_; 
v_unused_2392_ = lean_ctor_get(v_b_2354_, 1);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_b_2354_, 0);
lean_dec(v_unused_2393_);
v___x_2381_ = v_b_2354_;
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v_b_2354_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v_a_2383_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2384_ = l_Lean_Meta_FVarSubst_erase(v_subst_2370_, v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 2, v___x_2384_);
lean_ctor_set(v___x_2372_, 0, v_a_2383_);
v___x_2386_ = v___x_2372_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2383_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_fields_2369_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2386_);
v___x_2388_ = v___x_2381_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_ctorName_2367_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
v_a_2361_ = v___x_2388_;
goto v___jp_2360_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2412_; 
lean_del_object(v___x_2372_);
lean_dec(v_subst_2370_);
lean_dec_ref(v_fields_2369_);
v_a_2394_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2396_ = v___x_2379_;
v_isShared_2397_ = v_isSharedCheck_2412_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2379_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2412_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
lean_inc(v_a_2394_);
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
uint8_t v___x_2400_; 
v___x_2400_ = l_Lean_Exception_isInterrupt(v_a_2394_);
if (v___x_2400_ == 0)
{
uint8_t v___x_2401_; 
v___x_2401_ = l_Lean_Exception_isRuntime(v_a_2394_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
lean_dec_ref(v___x_2399_);
v___x_2402_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2378_, v___y_2356_, v___y_2358_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_dec_ref_known(v___x_2402_, 1);
v_a_2361_ = v_b_2354_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref(v_b_2354_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_dec(v_a_2378_);
lean_dec_ref(v_b_2354_);
return v___x_2399_;
}
}
else
{
lean_dec(v_a_2394_);
lean_dec(v_a_2378_);
lean_dec_ref(v_b_2354_);
return v___x_2399_;
}
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_fvarId_2376_);
lean_del_object(v___x_2372_);
lean_dec(v_subst_2370_);
lean_dec_ref(v_fields_2369_);
lean_dec(v_mvarId_2368_);
lean_dec_ref(v_b_2354_);
v_a_2413_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2377_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2377_);
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
lean_dec_ref(v___x_2375_);
lean_del_object(v___x_2372_);
lean_dec(v_subst_2370_);
lean_dec_ref(v_fields_2369_);
lean_dec(v_mvarId_2368_);
v_a_2361_ = v_b_2354_;
goto v___jp_2360_;
}
}
}
else
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v_b_2354_);
return v___x_2422_;
}
v___jp_2360_:
{
size_t v___x_2362_; size_t v___x_2363_; 
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2352_, v___x_2362_);
v_i_2352_ = v___x_2363_;
v_b_2354_ = v_a_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2423_, lean_object* v_i_2424_, lean_object* v_stop_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
size_t v_i_boxed_2432_; size_t v_stop_boxed_2433_; lean_object* v_res_2434_; 
v_i_boxed_2432_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_stop_boxed_2433_ = lean_unbox_usize(v_stop_2425_);
lean_dec(v_stop_2425_);
v_res_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2423_, v_i_boxed_2432_, v_stop_boxed_2433_, v_b_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_as_2423_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2435_, size_t v_sz_2436_, size_t v_i_2437_, lean_object* v_bs_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
uint8_t v___x_2444_; 
v___x_2444_ = lean_usize_dec_lt(v_i_2437_, v_sz_2436_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_bs_2438_);
return v___x_2445_;
}
else
{
lean_object* v_v_2446_; lean_object* v___x_2447_; lean_object* v_bs_x27_2448_; lean_object* v_a_2450_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_v_2446_ = lean_array_uget(v_bs_2438_, v_i_2437_);
v___x_2447_ = lean_unsigned_to_nat(0u);
v_bs_x27_2448_ = lean_array_uset(v_bs_2438_, v_i_2437_, v___x_2447_);
v___x_2455_ = lean_array_get_size(v_indicesFVarIds_2435_);
v___x_2456_ = lean_nat_dec_lt(v___x_2447_, v___x_2455_);
if (v___x_2456_ == 0)
{
v_a_2450_ = v_v_2446_;
goto v___jp_2449_;
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((size_t)0ULL);
v___x_2458_ = lean_usize_of_nat(v___x_2455_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2435_, v___x_2457_, v___x_2458_, v_v_2446_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v_a_2450_ = v_a_2460_;
goto v___jp_2449_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v_bs_x27_2448_);
v_a_2461_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2459_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
v___jp_2449_:
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_add(v_i_2437_, v___x_2451_);
v___x_2453_ = lean_array_uset(v_bs_x27_2448_, v_i_2437_, v_a_2450_);
v_i_2437_ = v___x_2452_;
v_bs_2438_ = v___x_2453_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2469_, lean_object* v_sz_2470_, lean_object* v_i_2471_, lean_object* v_bs_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
size_t v_sz_boxed_2478_; size_t v_i_boxed_2479_; lean_object* v_res_2480_; 
v_sz_boxed_2478_ = lean_unbox_usize(v_sz_2470_);
lean_dec(v_sz_2470_);
v_i_boxed_2479_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2469_, v_sz_boxed_2478_, v_i_boxed_2479_, v_bs_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_indicesFVarIds_2469_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2481_, lean_object* v_s_u2082_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_indicesFVarIds_2488_; size_t v_sz_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v_indicesFVarIds_2488_ = lean_ctor_get(v_s_u2081_2481_, 1);
v_sz_2489_ = lean_array_size(v_s_u2082_2482_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2488_, v_sz_2489_, v___x_2490_, v_s_u2082_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2492_, lean_object* v_s_u2082_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2492_, v_s_u2082_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec_ref(v_s_u2081_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2500_, lean_object* v_us_2501_, lean_object* v_params_2502_, lean_object* v_majorFVarId_2503_, size_t v_sz_2504_, size_t v_i_2505_, lean_object* v_bs_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_lt(v_i_2505_, v_sz_2504_);
if (v___x_2507_ == 0)
{
lean_dec(v_majorFVarId_2503_);
lean_dec(v_us_2501_);
return v_bs_2506_;
}
else
{
lean_object* v_v_2508_; lean_object* v___x_2509_; lean_object* v_bs_x27_2510_; lean_object* v___y_2512_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_v_2508_ = lean_array_uget(v_bs_2506_, v_i_2505_);
v___x_2509_ = lean_unsigned_to_nat(0u);
v_bs_x27_2510_ = lean_array_uset(v_bs_2506_, v_i_2505_, v___x_2509_);
v___x_2517_ = lean_usize_to_nat(v_i_2505_);
v___x_2518_ = lean_array_get_size(v_ctorNames_2500_);
v___x_2519_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_v_2508_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___y_2512_ = v___x_2521_;
goto v___jp_2511_;
}
else
{
lean_object* v_mvarId_2522_; lean_object* v_fields_2523_; lean_object* v_subst_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2539_; 
v_mvarId_2522_ = lean_ctor_get(v_v_2508_, 0);
v_fields_2523_ = lean_ctor_get(v_v_2508_, 1);
v_subst_2524_ = lean_ctor_get(v_v_2508_, 2);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_v_2508_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2526_ = v_v_2508_;
v_isShared_2527_ = v_isSharedCheck_2539_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_subst_2524_);
lean_inc(v_fields_2523_);
lean_inc(v_mvarId_2522_);
lean_dec(v_v_2508_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2539_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_ctorName_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_ctorApp_2531_; lean_object* v___x_2532_; lean_object* v_subst_2533_; lean_object* v___x_2535_; 
v_ctorName_2528_ = lean_array_fget_borrowed(v_ctorNames_2500_, v___x_2517_);
lean_dec(v___x_2517_);
lean_inc(v_us_2501_);
lean_inc(v_ctorName_2528_);
v___x_2529_ = l_Lean_mkConst(v_ctorName_2528_, v_us_2501_);
v___x_2530_ = l_Lean_mkAppN(v___x_2529_, v_params_2502_);
v_ctorApp_2531_ = l_Lean_mkAppN(v___x_2530_, v_fields_2523_);
v___x_2532_ = l_Lean_Meta_FVarSubst_erase(v_subst_2524_, v_majorFVarId_2503_);
lean_inc(v_majorFVarId_2503_);
v_subst_2533_ = l_Lean_Meta_FVarSubst_insert(v___x_2532_, v_majorFVarId_2503_, v_ctorApp_2531_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 2, v_subst_2533_);
v___x_2535_ = v___x_2526_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_mvarId_2522_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_fields_2523_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_subst_2533_);
v___x_2535_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_inc(v_ctorName_2528_);
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_ctorName_2528_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___y_2512_ = v___x_2537_;
goto v___jp_2511_;
}
}
}
v___jp_2511_:
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2505_, v___x_2513_);
v___x_2515_ = lean_array_uset(v_bs_x27_2510_, v_i_2505_, v___y_2512_);
v_i_2505_ = v___x_2514_;
v_bs_2506_ = v___x_2515_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2540_, lean_object* v_us_2541_, lean_object* v_params_2542_, lean_object* v_majorFVarId_2543_, lean_object* v_sz_2544_, lean_object* v_i_2545_, lean_object* v_bs_2546_){
_start:
{
size_t v_sz_boxed_2547_; size_t v_i_boxed_2548_; lean_object* v_res_2549_; 
v_sz_boxed_2547_ = lean_unbox_usize(v_sz_2544_);
lean_dec(v_sz_2544_);
v_i_boxed_2548_ = lean_unbox_usize(v_i_2545_);
lean_dec(v_i_2545_);
v_res_2549_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2540_, v_us_2541_, v_params_2542_, v_majorFVarId_2543_, v_sz_boxed_2547_, v_i_boxed_2548_, v_bs_2546_);
lean_dec_ref(v_params_2542_);
lean_dec_ref(v_ctorNames_2540_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2550_, lean_object* v_ctorNames_2551_, lean_object* v_majorFVarId_2552_, lean_object* v_us_2553_, lean_object* v_params_2554_){
_start:
{
size_t v_sz_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v_sz_2555_ = lean_array_size(v_s_2550_);
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2551_, v_us_2553_, v_params_2554_, v_majorFVarId_2552_, v_sz_2555_, v___x_2556_, v_s_2550_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2558_, lean_object* v_ctorNames_2559_, lean_object* v_majorFVarId_2560_, lean_object* v_us_2561_, lean_object* v_params_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2558_, v_ctorNames_2559_, v_majorFVarId_2560_, v_us_2561_, v_params_2562_);
lean_dec_ref(v_params_2562_);
lean_dec_ref(v_ctorNames_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2564_, lean_object* v_us_2565_, lean_object* v_params_2566_, lean_object* v_majorFVarId_2567_, lean_object* v_as_2568_, size_t v_sz_2569_, size_t v_i_2570_, lean_object* v_bs_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2564_, v_us_2565_, v_params_2566_, v_majorFVarId_2567_, v_sz_2569_, v_i_2570_, v_bs_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2573_, lean_object* v_us_2574_, lean_object* v_params_2575_, lean_object* v_majorFVarId_2576_, lean_object* v_as_2577_, lean_object* v_sz_2578_, lean_object* v_i_2579_, lean_object* v_bs_2580_){
_start:
{
size_t v_sz_boxed_2581_; size_t v_i_boxed_2582_; lean_object* v_res_2583_; 
v_sz_boxed_2581_ = lean_unbox_usize(v_sz_2578_);
lean_dec(v_sz_2578_);
v_i_boxed_2582_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_res_2583_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2573_, v_us_2574_, v_params_2575_, v_majorFVarId_2576_, v_as_2577_, v_sz_boxed_2581_, v_i_boxed_2582_, v_bs_2580_);
lean_dec_ref(v_as_2577_);
lean_dec_ref(v_params_2575_);
lean_dec_ref(v_ctorNames_2573_);
return v_res_2583_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = l_Lean_maxRecDepthErrorMessage;
v___x_2590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2592_ = l_Lean_MessageData_ofFormat(v___x_2591_);
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2594_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2595_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_ref_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2604_, lean_object* v_ref_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2605_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2612_, lean_object* v_ref_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2612_, v_ref_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2621_, lean_object* v_mvarId_2622_, lean_object* v_subst_2623_, lean_object* v_caseName_x3f_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_toCold_2630_; lean_object* v_currRecDepth_2631_; lean_object* v_ref_2632_; uint16_t v_optionFlags_2633_; uint8_t v_suppressElabErrors_2634_; uint8_t v_isRecordingDeps_2635_; lean_object* v_maxRecDepth_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; uint8_t v___x_2684_; 
v_toCold_2630_ = lean_ctor_get(v_a_2627_, 0);
lean_inc_ref(v_toCold_2630_);
v_currRecDepth_2631_ = lean_ctor_get(v_a_2627_, 1);
lean_inc(v_currRecDepth_2631_);
v_ref_2632_ = lean_ctor_get(v_a_2627_, 2);
lean_inc(v_ref_2632_);
v_optionFlags_2633_ = lean_ctor_get_uint16(v_a_2627_, sizeof(void*)*3);
v_suppressElabErrors_2634_ = lean_ctor_get_uint8(v_a_2627_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2635_ = lean_ctor_get_uint8(v_a_2627_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2627_);
v_maxRecDepth_2636_ = lean_ctor_get(v_toCold_2630_, 3);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_nat_dec_eq(v_numEqs_2621_, v___x_2637_);
v___x_2684_ = lean_nat_dec_eq(v_maxRecDepth_2636_, v___x_2637_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_nat_dec_eq(v_currRecDepth_2631_, v_maxRecDepth_2636_);
if (v___x_2685_ == 0)
{
goto v___jp_2639_;
}
else
{
lean_object* v___x_2686_; 
lean_dec(v_currRecDepth_2631_);
lean_dec_ref(v_toCold_2630_);
lean_dec(v_caseName_x3f_2624_);
lean_dec(v_subst_2623_);
lean_dec(v_mvarId_2622_);
lean_dec(v_numEqs_2621_);
v___x_2686_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2632_);
return v___x_2686_;
}
}
else
{
goto v___jp_2639_;
}
v___jp_2639_:
{
if (v___x_2638_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_add(v_currRecDepth_2631_, v___x_2640_);
lean_dec(v_currRecDepth_2631_);
v___x_2642_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2642_, 0, v_toCold_2630_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
lean_ctor_set(v___x_2642_, 2, v_ref_2632_);
lean_ctor_set_uint16(v___x_2642_, sizeof(void*)*3, v_optionFlags_2633_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*3 + 2, v_suppressElabErrors_2634_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*3 + 3, v_isRecordingDeps_2635_);
v___x_2643_ = l_Lean_Meta_intro1Core(v_mvarId_2622_, v___x_2638_, v_a_2625_, v_a_2626_, v___x_2642_, v_a_2628_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v_fst_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v_a_2644_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_a_2644_);
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2624_);
v___x_2648_ = l_Lean_Meta_unifyEq_x3f(v_snd_2646_, v_fst_2645_, v_subst_2623_, v___x_2647_, v_caseName_x3f_2624_, v_a_2625_, v_a_2626_, v___x_2642_, v_a_2628_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2664_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2664_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2664_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
if (lean_obj_tag(v_a_2649_) == 1)
{
lean_object* v_val_2653_; lean_object* v_mvarId_2654_; lean_object* v_subst_2655_; lean_object* v_numNewEqs_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_del_object(v___x_2651_);
v_val_2653_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_val_2653_);
lean_dec_ref_known(v_a_2649_, 1);
v_mvarId_2654_ = lean_ctor_get(v_val_2653_, 0);
lean_inc(v_mvarId_2654_);
v_subst_2655_ = lean_ctor_get(v_val_2653_, 1);
lean_inc(v_subst_2655_);
v_numNewEqs_2656_ = lean_ctor_get(v_val_2653_, 2);
lean_inc(v_numNewEqs_2656_);
lean_dec(v_val_2653_);
v___x_2657_ = lean_nat_sub(v_numEqs_2621_, v___x_2640_);
lean_dec(v_numEqs_2621_);
v___x_2658_ = lean_nat_add(v___x_2657_, v_numNewEqs_2656_);
lean_dec(v_numNewEqs_2656_);
lean_dec(v___x_2657_);
v_numEqs_2621_ = v___x_2658_;
v_mvarId_2622_ = v_mvarId_2654_;
v_subst_2623_ = v_subst_2655_;
v_a_2627_ = v___x_2642_;
goto _start;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
lean_dec(v_a_2649_);
lean_dec_ref_known(v___x_2642_, 3);
lean_dec(v_caseName_x3f_2624_);
lean_dec(v_numEqs_2621_);
v___x_2660_ = lean_box(0);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2660_);
v___x_2662_ = v___x_2651_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref_known(v___x_2642_, 3);
lean_dec(v_caseName_x3f_2624_);
lean_dec(v_numEqs_2621_);
v_a_2665_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2648_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2648_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref_known(v___x_2642_, 3);
lean_dec(v_caseName_x3f_2624_);
lean_dec(v_subst_2623_);
lean_dec(v_numEqs_2621_);
v_a_2673_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2643_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2643_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec(v_ref_2632_);
lean_dec(v_currRecDepth_2631_);
lean_dec_ref(v_toCold_2630_);
lean_dec(v_caseName_x3f_2624_);
lean_dec(v_numEqs_2621_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_mvarId_2622_);
lean_ctor_set(v___x_2681_, 1, v_subst_2623_);
v___x_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2687_, lean_object* v_mvarId_2688_, lean_object* v_subst_2689_, lean_object* v_caseName_x3f_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2687_, v_mvarId_2688_, v_subst_2689_, v_caseName_x3f_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2697_, size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_bs_2700_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2701_ == 0)
{
lean_dec(v_snd_2697_);
return v_bs_2700_;
}
else
{
lean_object* v_v_2702_; lean_object* v___x_2703_; lean_object* v_bs_x27_2704_; lean_object* v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v_v_2702_ = lean_array_uget(v_bs_2700_, v_i_2699_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v_bs_x27_2704_ = lean_array_uset(v_bs_2700_, v_i_2699_, v___x_2703_);
lean_inc(v_snd_2697_);
v___x_2705_ = l_Lean_Meta_FVarSubst_apply(v_snd_2697_, v_v_2702_);
lean_dec(v_v_2702_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2699_, v___x_2706_);
v___x_2708_ = lean_array_uset(v_bs_x27_2704_, v_i_2699_, v___x_2705_);
v_i_2699_ = v___x_2707_;
v_bs_2700_ = v___x_2708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2710_, lean_object* v_sz_2711_, lean_object* v_i_2712_, lean_object* v_bs_2713_){
_start:
{
size_t v_sz_boxed_2714_; size_t v_i_boxed_2715_; lean_object* v_res_2716_; 
v_sz_boxed_2714_ = lean_unbox_usize(v_sz_2711_);
lean_dec(v_sz_2711_);
v_i_boxed_2715_ = lean_unbox_usize(v_i_2712_);
lean_dec(v_i_2712_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2710_, v_sz_boxed_2714_, v_i_boxed_2715_, v_bs_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2717_, lean_object* v_as_2718_, size_t v_i_2719_, size_t v_stop_2720_, lean_object* v_b_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_a_2728_; uint8_t v___x_2732_; 
v___x_2732_ = lean_usize_dec_eq(v_i_2719_, v_stop_2720_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v_toInductionSubgoal_2734_; lean_object* v_ctorName_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2769_; 
v___x_2733_ = lean_array_uget(v_as_2718_, v_i_2719_);
v_toInductionSubgoal_2734_ = lean_ctor_get(v___x_2733_, 0);
v_ctorName_2735_ = lean_ctor_get(v___x_2733_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2769_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_ctorName_2735_);
lean_inc(v_toInductionSubgoal_2734_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2769_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_mvarId_2739_; lean_object* v_fields_2740_; lean_object* v_subst_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2768_; 
v_mvarId_2739_ = lean_ctor_get(v_toInductionSubgoal_2734_, 0);
v_fields_2740_ = lean_ctor_get(v_toInductionSubgoal_2734_, 1);
v_subst_2741_ = lean_ctor_get(v_toInductionSubgoal_2734_, 2);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_toInductionSubgoal_2734_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2743_ = v_toInductionSubgoal_2734_;
v_isShared_2744_ = v_isSharedCheck_2768_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_subst_2741_);
lean_inc(v_fields_2740_);
lean_inc(v_mvarId_2739_);
lean_dec(v_toInductionSubgoal_2734_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2768_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; 
lean_inc_ref(v___y_2724_);
lean_inc(v_ctorName_2735_);
lean_inc(v_numEqs_2717_);
v___x_2745_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2717_, v_mvarId_2739_, v_subst_2741_, v_ctorName_2735_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
if (lean_obj_tag(v_a_2746_) == 0)
{
lean_del_object(v___x_2743_);
lean_dec_ref(v_fields_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_ctorName_2735_);
v_a_2728_ = v_b_2721_;
goto v___jp_2727_;
}
else
{
lean_object* v_val_2747_; lean_object* v_fst_2748_; lean_object* v_snd_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v_val_2747_ = lean_ctor_get(v_a_2746_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v_a_2746_, 1);
v_fst_2748_ = lean_ctor_get(v_val_2747_, 0);
lean_inc(v_fst_2748_);
v_snd_2749_ = lean_ctor_get(v_val_2747_, 1);
lean_inc_n(v_snd_2749_, 2);
lean_dec(v_val_2747_);
v_sz_2750_ = lean_array_size(v_fields_2740_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2749_, v_sz_2750_, v___x_2751_, v_fields_2740_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 2, v_snd_2749_);
lean_ctor_set(v___x_2743_, 1, v___x_2752_);
lean_ctor_set(v___x_2743_, 0, v_fst_2748_);
v___x_2754_ = v___x_2743_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_fst_2748_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_snd_2749_);
v___x_2754_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2756_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2754_);
v___x_2756_ = v___x_2737_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_ctorName_2735_);
v___x_2756_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_array_push(v_b_2721_, v___x_2756_);
v_a_2728_ = v___x_2757_;
goto v___jp_2727_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_del_object(v___x_2743_);
lean_dec_ref(v_fields_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_ctorName_2735_);
lean_dec_ref(v_b_2721_);
lean_dec(v_numEqs_2717_);
v_a_2760_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2745_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2745_);
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
}
}
else
{
lean_object* v___x_2770_; 
lean_dec(v_numEqs_2717_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_b_2721_);
return v___x_2770_;
}
v___jp_2727_:
{
size_t v___x_2729_; size_t v___x_2730_; 
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_add(v_i_2719_, v___x_2729_);
v_i_2719_ = v___x_2730_;
v_b_2721_ = v_a_2728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2771_, lean_object* v_as_2772_, lean_object* v_i_2773_, lean_object* v_stop_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
size_t v_i_boxed_2781_; size_t v_stop_boxed_2782_; lean_object* v_res_2783_; 
v_i_boxed_2781_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_stop_boxed_2782_ = lean_unbox_usize(v_stop_2774_);
lean_dec(v_stop_2774_);
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2771_, v_as_2772_, v_i_boxed_2781_, v_stop_boxed_2782_, v_b_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_as_2772_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2786_, lean_object* v_as_2787_, lean_object* v_start_2788_, lean_object* v_stop_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2796_ = lean_nat_dec_lt(v_start_2788_, v_stop_2789_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
lean_dec(v_numEqs_2786_);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
return v___x_2797_;
}
else
{
lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = lean_array_get_size(v_as_2787_);
v___x_2799_ = lean_nat_dec_le(v_stop_2789_, v___x_2798_);
if (v___x_2799_ == 0)
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_nat_dec_lt(v_start_2788_, v___x_2798_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec(v_numEqs_2786_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2795_);
return v___x_2801_;
}
else
{
size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_usize_of_nat(v_start_2788_);
v___x_2803_ = lean_usize_of_nat(v___x_2798_);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2786_, v_as_2787_, v___x_2802_, v___x_2803_, v___x_2795_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v___x_2804_;
}
}
else
{
size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = lean_usize_of_nat(v_start_2788_);
v___x_2806_ = lean_usize_of_nat(v_stop_2789_);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2786_, v_as_2787_, v___x_2805_, v___x_2806_, v___x_2795_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2808_, lean_object* v_as_2809_, lean_object* v_start_2810_, lean_object* v_stop_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2808_, v_as_2809_, v_start_2810_, v_stop_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v_stop_2811_);
lean_dec(v_start_2810_);
lean_dec_ref(v_as_2809_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2818_, lean_object* v_subgoals_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_array_get_size(v_subgoals_2819_);
v___x_2827_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2818_, v_subgoals_2819_, v___x_2825_, v___x_2826_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2828_, lean_object* v_subgoals_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2828_, v_subgoals_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec_ref(v_subgoals_2829_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2847_, lean_object* v_ctx_2848_, lean_object* v_mvarId_2849_, lean_object* v_majorFVarId_2850_, lean_object* v_givenNames_2851_, uint8_t v_useNatCasesAuxOn_2852_, lean_object* v_interestingCtors_x3f_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
lean_inc(v___y_2857_);
lean_inc_ref(v___y_2856_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
v___x_2859_ = lean_infer_type(v___x_2847_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2860_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_fst_2863_; lean_object* v_snd_2864_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_fst_2863_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_fst_2863_);
v_snd_2864_ = lean_ctor_get(v_a_2862_, 1);
lean_inc(v_snd_2864_);
lean_dec(v_a_2862_);
if (lean_obj_tag(v_interestingCtors_x3f_2853_) == 1)
{
lean_object* v_val_2915_; lean_object* v___x_2916_; lean_object* v_env_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; uint8_t v___x_2920_; lean_object* v___x_2921_; 
v_val_2915_ = lean_ctor_get(v_interestingCtors_x3f_2853_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v_interestingCtors_x3f_2853_, 1);
v___x_2916_ = lean_st_ref_get(v___y_2857_);
v_env_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_ref(v_env_2917_);
lean_dec(v___x_2916_);
v___x_2918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2919_ = 1;
v___x_2920_ = l_Lean_Environment_contains(v_env_2917_, v___x_2918_, v___x_2919_);
v___x_2921_ = lean_st_ref_get(v___y_2857_);
if (v___x_2920_ == 0)
{
lean_dec(v___x_2921_);
lean_dec(v_val_2915_);
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
v___y_2905_ = v___y_2857_;
goto v___jp_2901_;
}
else
{
lean_object* v_inductiveVal_2922_; lean_object* v_toConstantVal_2923_; lean_object* v_ctors_2924_; lean_object* v_name_2925_; lean_object* v_env_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v_inductiveVal_2922_ = lean_ctor_get(v_ctx_2848_, 0);
v_toConstantVal_2923_ = lean_ctor_get(v_inductiveVal_2922_, 0);
v_ctors_2924_ = lean_ctor_get(v_inductiveVal_2922_, 4);
v_name_2925_ = lean_ctor_get(v_toConstantVal_2923_, 0);
v_env_2926_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_ref(v_env_2926_);
lean_dec(v___x_2921_);
lean_inc(v_name_2925_);
v___x_2927_ = l_Lean_mkCtorIdxName(v_name_2925_);
v___x_2928_ = l_Lean_Environment_contains(v_env_2926_, v___x_2927_, v___x_2919_);
if (v___x_2928_ == 0)
{
lean_dec(v_val_2915_);
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
v___y_2905_ = v___y_2857_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_array_get_size(v_val_2915_);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_nat_dec_eq(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = l_List_lengthTR___redArg(v_ctors_2924_);
v___x_2933_ = lean_nat_dec_lt(v___x_2929_, v___x_2932_);
lean_dec(v___x_2932_);
if (v___x_2933_ == 0)
{
lean_dec(v_val_2915_);
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
v___y_2905_ = v___y_2857_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2934_; 
lean_inc(v_name_2925_);
lean_dec_ref(v_ctx_2848_);
lean_inc(v_val_2915_);
v___x_2934_ = l_Lean_Meta_mkSparseCasesOn(v_name_2925_, v_val_2915_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
lean_inc(v_majorFVarId_2850_);
v___x_2936_ = l_Lean_MVarId_induction(v_mvarId_2849_, v_majorFVarId_2850_, v_a_2935_, v_givenNames_2851_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2945_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2937_, v_val_2915_, v_majorFVarId_2850_, v_fst_2863_, v_snd_2864_);
lean_dec(v_snd_2864_);
lean_dec(v_val_2915_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_val_2915_);
lean_dec(v_snd_2864_);
lean_dec(v_fst_2863_);
lean_dec(v_majorFVarId_2850_);
v_a_2946_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2936_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2936_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_val_2915_);
lean_dec(v_snd_2864_);
lean_dec(v_fst_2863_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_givenNames_2851_);
lean_dec(v_majorFVarId_2850_);
lean_dec(v_mvarId_2849_);
v_a_2954_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2934_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2934_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
else
{
lean_dec(v_val_2915_);
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
v___y_2905_ = v___y_2857_;
goto v___jp_2901_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2853_);
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
v___y_2905_ = v___y_2857_;
goto v___jp_2901_;
}
v___jp_2865_:
{
lean_object* v_inductiveVal_2871_; lean_object* v_ctors_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_inductiveVal_2871_ = lean_ctor_get(v_ctx_2848_, 0);
lean_inc_ref(v_inductiveVal_2871_);
lean_dec_ref(v_ctx_2848_);
v_ctors_2872_ = lean_ctor_get(v_inductiveVal_2871_, 4);
lean_inc(v_ctors_2872_);
lean_dec_ref(v_inductiveVal_2871_);
v___x_2873_ = lean_array_mk(v_ctors_2872_);
lean_inc(v_majorFVarId_2850_);
v___x_2874_ = l_Lean_MVarId_induction(v_mvarId_2849_, v_majorFVarId_2850_, v___y_2870_, v_givenNames_2851_, v___y_2868_, v___y_2867_, v___y_2866_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2868_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2875_, v___x_2873_, v_majorFVarId_2850_, v_fst_2863_, v_snd_2864_);
lean_dec(v_snd_2864_);
lean_dec_ref(v___x_2873_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref(v___x_2873_);
lean_dec(v_snd_2864_);
lean_dec(v_fst_2863_);
lean_dec(v_majorFVarId_2850_);
v_a_2884_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2874_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2874_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
v___jp_2892_:
{
lean_object* v_inductiveVal_2897_; lean_object* v_toConstantVal_2898_; lean_object* v_name_2899_; lean_object* v___x_2900_; 
v_inductiveVal_2897_ = lean_ctor_get(v_ctx_2848_, 0);
v_toConstantVal_2898_ = lean_ctor_get(v_inductiveVal_2897_, 0);
v_name_2899_ = lean_ctor_get(v_toConstantVal_2898_, 0);
lean_inc(v_name_2899_);
v___x_2900_ = l_Lean_mkCasesOnName(v_name_2899_);
v___y_2866_ = v___y_2893_;
v___y_2867_ = v___y_2895_;
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2896_;
v___y_2870_ = v___x_2900_;
goto v___jp_2865_;
}
v___jp_2901_:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_st_ref_get(v___y_2905_);
if (v_useNatCasesAuxOn_2852_ == 0)
{
lean_dec(v___x_2906_);
v___y_2893_ = v___y_2904_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2903_;
v___y_2896_ = v___y_2905_;
goto v___jp_2892_;
}
else
{
lean_object* v_inductiveVal_2907_; lean_object* v_toConstantVal_2908_; lean_object* v_env_2909_; lean_object* v_name_2910_; lean_object* v___x_2911_; uint8_t v___x_2912_; 
v_inductiveVal_2907_ = lean_ctor_get(v_ctx_2848_, 0);
v_toConstantVal_2908_ = lean_ctor_get(v_inductiveVal_2907_, 0);
v_env_2909_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2906_);
v_name_2910_ = lean_ctor_get(v_toConstantVal_2908_, 0);
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2912_ = lean_name_eq(v_name_2910_, v___x_2911_);
if (v___x_2912_ == 0)
{
lean_dec_ref(v_env_2909_);
v___y_2893_ = v___y_2904_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2903_;
v___y_2896_ = v___y_2905_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2914_ = l_Lean_Environment_contains(v_env_2909_, v___x_2913_, v___x_2912_);
if (v___x_2914_ == 0)
{
v___y_2893_ = v___y_2904_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2903_;
v___y_2896_ = v___y_2905_;
goto v___jp_2892_;
}
else
{
v___y_2866_ = v___y_2904_;
v___y_2867_ = v___y_2903_;
v___y_2868_ = v___y_2902_;
v___y_2869_ = v___y_2905_;
v___y_2870_ = v___x_2913_;
goto v___jp_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v_interestingCtors_x3f_2853_);
lean_dec_ref(v_givenNames_2851_);
lean_dec(v_majorFVarId_2850_);
lean_dec(v_mvarId_2849_);
lean_dec_ref(v_ctx_2848_);
v_a_2962_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2861_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2861_);
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
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v_interestingCtors_x3f_2853_);
lean_dec_ref(v_givenNames_2851_);
lean_dec(v_majorFVarId_2850_);
lean_dec(v_mvarId_2849_);
lean_dec_ref(v_ctx_2848_);
v_a_2970_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2859_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2859_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_2978_, lean_object* v_ctx_2979_, lean_object* v_mvarId_2980_, lean_object* v_majorFVarId_2981_, lean_object* v_givenNames_2982_, lean_object* v_useNatCasesAuxOn_2983_, lean_object* v_interestingCtors_x3f_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_2990_; lean_object* v_res_2991_; 
v_useNatCasesAuxOn_boxed_2990_ = lean_unbox(v_useNatCasesAuxOn_2983_);
v_res_2991_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_2978_, v_ctx_2979_, v_mvarId_2980_, v_majorFVarId_2981_, v_givenNames_2982_, v_useNatCasesAuxOn_boxed_2990_, v_interestingCtors_x3f_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_2992_, lean_object* v_majorFVarId_2993_, lean_object* v_givenNames_2994_, lean_object* v_ctx_2995_, uint8_t v_useNatCasesAuxOn_2996_, lean_object* v_interestingCtors_x3f_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; 
lean_inc(v_majorFVarId_2993_);
v___x_3003_ = l_Lean_mkFVar(v_majorFVarId_2993_);
v___x_3004_ = lean_box(v_useNatCasesAuxOn_2996_);
lean_inc(v_mvarId_2992_);
v___f_3005_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3005_, 0, v___x_3003_);
lean_closure_set(v___f_3005_, 1, v_ctx_2995_);
lean_closure_set(v___f_3005_, 2, v_mvarId_2992_);
lean_closure_set(v___f_3005_, 3, v_majorFVarId_2993_);
lean_closure_set(v___f_3005_, 4, v_givenNames_2994_);
lean_closure_set(v___f_3005_, 5, v___x_3004_);
lean_closure_set(v___f_3005_, 6, v_interestingCtors_x3f_2997_);
v___x_3006_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_2992_, v___f_3005_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3007_, lean_object* v_majorFVarId_3008_, lean_object* v_givenNames_3009_, lean_object* v_ctx_3010_, lean_object* v_useNatCasesAuxOn_3011_, lean_object* v_interestingCtors_x3f_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3018_; lean_object* v_res_3019_; 
v_useNatCasesAuxOn_boxed_3018_ = lean_unbox(v_useNatCasesAuxOn_3011_);
v_res_3019_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3007_, v_majorFVarId_3008_, v_givenNames_3009_, v_ctx_3010_, v_useNatCasesAuxOn_boxed_3018_, v_interestingCtors_x3f_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
return v_res_3019_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3020_; double v___x_3021_; 
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_float_of_nat(v___x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3025_, lean_object* v_msg_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_ref_3032_; lean_object* v___x_3033_; lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3079_; 
v_ref_3032_ = lean_ctor_get(v___y_3029_, 2);
v___x_3033_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3079_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3079_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v_traceState_3039_; lean_object* v_env_3040_; lean_object* v_nextMacroScope_3041_; lean_object* v_ngen_3042_; lean_object* v_auxDeclNGen_3043_; lean_object* v_cache_3044_; lean_object* v_recordedDeps_3045_; lean_object* v_messages_3046_; lean_object* v_infoState_3047_; lean_object* v_snapshotTasks_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3078_; 
v___x_3038_ = lean_st_ref_take(v___y_3030_);
v_traceState_3039_ = lean_ctor_get(v___x_3038_, 4);
v_env_3040_ = lean_ctor_get(v___x_3038_, 0);
v_nextMacroScope_3041_ = lean_ctor_get(v___x_3038_, 1);
v_ngen_3042_ = lean_ctor_get(v___x_3038_, 2);
v_auxDeclNGen_3043_ = lean_ctor_get(v___x_3038_, 3);
v_cache_3044_ = lean_ctor_get(v___x_3038_, 5);
v_recordedDeps_3045_ = lean_ctor_get(v___x_3038_, 6);
v_messages_3046_ = lean_ctor_get(v___x_3038_, 7);
v_infoState_3047_ = lean_ctor_get(v___x_3038_, 8);
v_snapshotTasks_3048_ = lean_ctor_get(v___x_3038_, 9);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3050_ = v___x_3038_;
v_isShared_3051_ = v_isSharedCheck_3078_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_snapshotTasks_3048_);
lean_inc(v_infoState_3047_);
lean_inc(v_messages_3046_);
lean_inc(v_recordedDeps_3045_);
lean_inc(v_cache_3044_);
lean_inc(v_traceState_3039_);
lean_inc(v_auxDeclNGen_3043_);
lean_inc(v_ngen_3042_);
lean_inc(v_nextMacroScope_3041_);
lean_inc(v_env_3040_);
lean_dec(v___x_3038_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3078_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
uint64_t v_tid_3052_; lean_object* v_traces_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3077_; 
v_tid_3052_ = lean_ctor_get_uint64(v_traceState_3039_, sizeof(void*)*1);
v_traces_3053_ = lean_ctor_get(v_traceState_3039_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_traceState_3039_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3055_ = v_traceState_3039_;
v_isShared_3056_ = v_isSharedCheck_3077_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_traces_3053_);
lean_dec(v_traceState_3039_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3077_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; double v___x_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3057_ = lean_box(0);
v___x_3058_ = lean_box(0);
v___x_3059_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3060_ = 0;
v___x_3061_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3062_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3062_, 0, v_cls_3025_);
lean_ctor_set(v___x_3062_, 1, v___x_3058_);
lean_ctor_set(v___x_3062_, 2, v___x_3061_);
lean_ctor_set_float(v___x_3062_, sizeof(void*)*3, v___x_3059_);
lean_ctor_set_float(v___x_3062_, sizeof(void*)*3 + 8, v___x_3059_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*3 + 16, v___x_3060_);
v___x_3063_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3064_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v_a_3034_);
lean_ctor_set(v___x_3064_, 2, v___x_3063_);
lean_inc(v_ref_3032_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_ref_3032_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Lean_PersistentArray_push___redArg(v_traces_3053_, v___x_3065_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3066_);
v___x_3068_ = v___x_3055_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3066_);
lean_ctor_set_uint64(v_reuseFailAlloc_3076_, sizeof(void*)*1, v_tid_3052_);
v___x_3068_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3070_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 4, v___x_3068_);
v___x_3070_ = v___x_3050_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_env_3040_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_nextMacroScope_3041_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_ngen_3042_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_auxDeclNGen_3043_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_cache_3044_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_recordedDeps_3045_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_messages_3046_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_infoState_3047_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_snapshotTasks_3048_);
v___x_3070_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_st_ref_put(v___y_3030_, v___x_3070_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3057_);
v___x_3073_ = v___x_3036_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3057_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3080_, lean_object* v_msg_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3080_, v_msg_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
return v_res_3087_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3092_ = l_Lean_MessageData_ofFormat(v___x_3091_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3102_ = l_Lean_stringToMessageData(v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3103_, lean_object* v___x_3104_, lean_object* v_majorFVarId_3105_, lean_object* v_givenNames_3106_, lean_object* v_interestingCtors_x3f_3107_, lean_object* v___x_3108_, uint8_t v_useNatCasesAuxOn_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
lean_inc(v___x_3104_);
lean_inc(v_mvarId_3103_);
v___x_3115_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3103_, v___x_3104_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; 
lean_dec_ref_known(v___x_3115_, 1);
lean_inc(v_majorFVarId_3105_);
v___x_3116_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3105_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
if (lean_obj_tag(v_a_3117_) == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref(v___x_3108_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
lean_dec(v_majorFVarId_3105_);
v___x_3118_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3119_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3104_, v_mvarId_3103_, v___x_3118_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3119_;
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v___x_3104_);
v_val_3120_ = lean_ctor_get(v_a_3117_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_a_3117_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3122_ = v_a_3117_;
v_isShared_3123_ = v_isSharedCheck_3185_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v_a_3117_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3185_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; 
lean_inc(v_val_3120_);
v___x_3124_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3120_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; uint8_t v___x_3126_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3124_, 1);
v___x_3126_ = lean_unbox(v_a_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Meta_generalizeIndices(v_mvarId_3103_, v_majorFVarId_3105_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v_toCold_3143_; lean_object* v_options_3144_; uint8_t v_hasTrace_3145_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_toCold_3143_ = lean_ctor_get(v___y_3112_, 0);
v_options_3144_ = lean_ctor_get(v_toCold_3143_, 2);
v_hasTrace_3145_ = lean_ctor_get_uint8(v_options_3144_, sizeof(void*)*1);
if (v_hasTrace_3145_ == 0)
{
lean_del_object(v___x_3122_);
lean_dec_ref(v___x_3108_);
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
v___y_3133_ = v___y_3113_;
goto v___jp_3129_;
}
else
{
lean_object* v_inheritedTraceOptions_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_inheritedTraceOptions_3146_ = lean_ctor_get(v_toCold_3143_, 11);
v___x_3147_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3148_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3149_ = l_Lean_Name_mkStr3(v___x_3147_, v___x_3148_, v___x_3108_);
v___x_3150_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3149_);
v___x_3151_ = l_Lean_Name_append(v___x_3150_, v___x_3149_);
v___x_3152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3146_, v_options_3144_, v___x_3151_);
lean_dec(v___x_3151_);
if (v___x_3152_ == 0)
{
lean_dec(v___x_3149_);
lean_del_object(v___x_3122_);
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
v___y_3133_ = v___y_3113_;
goto v___jp_3129_;
}
else
{
lean_object* v_mvarId_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v_mvarId_3153_ = lean_ctor_get(v_a_3128_, 0);
v___x_3154_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3153_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v_mvarId_3153_);
v___x_3156_ = v___x_3122_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_mvarId_3153_);
v___x_3156_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3154_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3149_, v___x_3157_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_dec_ref_known(v___x_3158_, 1);
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
v___y_3133_ = v___y_3113_;
goto v___jp_3129_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_a_3128_);
lean_dec(v_a_3125_);
lean_dec(v_val_3120_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
}
v___jp_3129_:
{
lean_object* v_mvarId_3134_; lean_object* v_fvarId_3135_; lean_object* v_numEqs_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; 
v_mvarId_3134_ = lean_ctor_get(v_a_3128_, 0);
v_fvarId_3135_ = lean_ctor_get(v_a_3128_, 2);
v_numEqs_3136_ = lean_ctor_get(v_a_3128_, 3);
lean_inc(v_numEqs_3136_);
v___x_3137_ = lean_unbox(v_a_3125_);
lean_dec(v_a_3125_);
lean_inc(v_fvarId_3135_);
lean_inc(v_mvarId_3134_);
v___x_3138_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3134_, v_fvarId_3135_, v_givenNames_3106_, v_val_3120_, v___x_3137_, v_interestingCtors_x3f_3107_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3140_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3128_, v_a_3139_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v_a_3128_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3136_, v_a_3141_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v_a_3141_);
return v___x_3142_;
}
else
{
lean_dec(v_numEqs_3136_);
return v___x_3140_;
}
}
else
{
lean_dec(v_numEqs_3136_);
lean_dec(v_a_3128_);
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_3125_);
lean_del_object(v___x_3122_);
lean_dec(v_val_3120_);
lean_dec_ref(v___x_3108_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
v_a_3168_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3127_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3127_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3176_; 
lean_dec(v_a_3125_);
lean_del_object(v___x_3122_);
lean_dec_ref(v___x_3108_);
v___x_3176_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3103_, v_majorFVarId_3105_, v_givenNames_3106_, v_val_3120_, v_useNatCasesAuxOn_3109_, v_interestingCtors_x3f_3107_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3176_;
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_del_object(v___x_3122_);
lean_dec(v_val_3120_);
lean_dec_ref(v___x_3108_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
lean_dec(v_majorFVarId_3105_);
lean_dec(v_mvarId_3103_);
v_a_3177_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3124_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3124_);
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
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v___x_3108_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
lean_dec(v_majorFVarId_3105_);
lean_dec(v___x_3104_);
lean_dec(v_mvarId_3103_);
v_a_3186_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3116_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3116_);
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
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___x_3108_);
lean_dec(v_interestingCtors_x3f_3107_);
lean_dec_ref(v_givenNames_3106_);
lean_dec(v_majorFVarId_3105_);
lean_dec(v___x_3104_);
lean_dec(v_mvarId_3103_);
v_a_3194_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3115_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3115_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3202_, lean_object* v___x_3203_, lean_object* v_majorFVarId_3204_, lean_object* v_givenNames_3205_, lean_object* v_interestingCtors_x3f_3206_, lean_object* v___x_3207_, lean_object* v_useNatCasesAuxOn_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3214_; lean_object* v_res_3215_; 
v_useNatCasesAuxOn_boxed_3214_ = lean_unbox(v_useNatCasesAuxOn_3208_);
v_res_3215_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3202_, v___x_3203_, v_majorFVarId_3204_, v_givenNames_3205_, v_interestingCtors_x3f_3206_, v___x_3207_, v_useNatCasesAuxOn_boxed_3214_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3219_, lean_object* v_majorFVarId_3220_, lean_object* v_givenNames_3221_, uint8_t v_useNatCasesAuxOn_3222_, lean_object* v_interestingCtors_x3f_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___f_3232_; lean_object* v___x_3233_; 
v___x_3229_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3230_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3231_ = lean_box(v_useNatCasesAuxOn_3222_);
lean_inc(v_mvarId_3219_);
v___f_3232_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3232_, 0, v_mvarId_3219_);
lean_closure_set(v___f_3232_, 1, v___x_3230_);
lean_closure_set(v___f_3232_, 2, v_majorFVarId_3220_);
lean_closure_set(v___f_3232_, 3, v_givenNames_3221_);
lean_closure_set(v___f_3232_, 4, v_interestingCtors_x3f_3223_);
lean_closure_set(v___f_3232_, 5, v___x_3229_);
lean_closure_set(v___f_3232_, 6, v___x_3231_);
v___x_3233_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3219_, v___f_3232_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3233_) == 0)
{
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; uint8_t v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v___x_3235_ = l_Lean_Exception_isInterrupt(v_a_3234_);
if (v___x_3235_ == 0)
{
uint8_t v___x_3236_; 
lean_inc(v_a_3234_);
v___x_3236_ = l_Lean_Exception_isRuntime(v_a_3234_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v___x_3237_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3230_, v_a_3234_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
return v___x_3237_;
}
else
{
return v___x_3233_;
}
}
else
{
return v___x_3233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3238_, lean_object* v_majorFVarId_3239_, lean_object* v_givenNames_3240_, lean_object* v_useNatCasesAuxOn_3241_, lean_object* v_interestingCtors_x3f_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3248_; lean_object* v_res_3249_; 
v_useNatCasesAuxOn_boxed_3248_ = lean_unbox(v_useNatCasesAuxOn_3241_);
v_res_3249_ = l_Lean_Meta_Cases_cases(v_mvarId_3238_, v_majorFVarId_3239_, v_givenNames_3240_, v_useNatCasesAuxOn_boxed_3248_, v_interestingCtors_x3f_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3250_, lean_object* v_majorFVarId_3251_, lean_object* v_givenNames_3252_, uint8_t v_useNatCasesAuxOn_3253_, lean_object* v_interestingCtors_x3f_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_Cases_cases(v_mvarId_3250_, v_majorFVarId_3251_, v_givenNames_3252_, v_useNatCasesAuxOn_3253_, v_interestingCtors_x3f_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3261_, lean_object* v_majorFVarId_3262_, lean_object* v_givenNames_3263_, lean_object* v_useNatCasesAuxOn_3264_, lean_object* v_interestingCtors_x3f_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3271_; lean_object* v_res_3272_; 
v_useNatCasesAuxOn_boxed_3271_ = lean_unbox(v_useNatCasesAuxOn_3264_);
v_res_3272_ = l_Lean_MVarId_cases(v_mvarId_3261_, v_majorFVarId_3262_, v_givenNames_3263_, v_useNatCasesAuxOn_boxed_3271_, v_interestingCtors_x3f_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_Meta_saveState___redArg(v___y_3275_, v___y_3277_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
v___x_3281_ = lean_apply_5(v_x_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, lean_box(0));
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_a_3280_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3290_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3290_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_a_3282_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3286_);
v___x_3288_ = v___x_3284_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3321_; 
v_a_3291_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3293_ = v___x_3281_;
v_isShared_3294_ = v_isSharedCheck_3321_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3281_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3321_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
uint8_t v___x_3295_; 
v___x_3295_ = l_Lean_Exception_isInterrupt(v_a_3291_);
if (v___x_3295_ == 0)
{
uint8_t v___x_3296_; 
lean_inc(v_a_3291_);
v___x_3296_ = l_Lean_Exception_isRuntime(v_a_3291_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
lean_del_object(v___x_3293_);
lean_dec(v_a_3291_);
v___x_3297_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3280_, v___y_3275_, v___y_3277_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3305_; 
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3306_);
v___x_3299_ = v___x_3297_;
v_isShared_3300_ = v_isSharedCheck_3305_;
goto v_resetjp_3298_;
}
else
{
lean_dec(v___x_3297_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3305_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = lean_box(0);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3301_);
v___x_3303_ = v___x_3299_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_a_3307_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3297_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3297_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v___x_3316_; 
lean_dec(v_a_3280_);
if (v_isShared_3294_ == 0)
{
v___x_3316_ = v___x_3293_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3291_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v___x_3319_; 
lean_dec(v_a_3280_);
if (v_isShared_3294_ == 0)
{
v___x_3319_ = v___x_3293_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3291_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v_x_3273_);
v_a_3322_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3279_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3279_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3337_, lean_object* v_x_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3345_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
if (lean_obj_tag(v_a_3353_) == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = l_List_reverse___redArg(v_a_3354_);
return v___x_3355_;
}
else
{
lean_object* v_head_3356_; lean_object* v_toInductionSubgoal_3357_; lean_object* v_tail_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3367_; 
v_head_3356_ = lean_ctor_get(v_a_3353_, 0);
v_toInductionSubgoal_3357_ = lean_ctor_get(v_head_3356_, 0);
lean_inc_ref(v_toInductionSubgoal_3357_);
v_tail_3358_ = lean_ctor_get(v_a_3353_, 1);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3367_ == 0)
{
lean_object* v_unused_3368_; 
v_unused_3368_ = lean_ctor_get(v_a_3353_, 0);
lean_dec(v_unused_3368_);
v___x_3360_ = v_a_3353_;
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_tail_3358_);
lean_dec(v_a_3353_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3367_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_mvarId_3362_; lean_object* v___x_3364_; 
v_mvarId_3362_ = lean_ctor_get(v_toInductionSubgoal_3357_, 0);
lean_inc(v_mvarId_3362_);
lean_dec_ref(v_toInductionSubgoal_3357_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v_a_3354_);
lean_ctor_set(v___x_3360_, 0, v_mvarId_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_mvarId_3362_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_a_3354_);
v___x_3364_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
v_a_3353_ = v_tail_3358_;
v_a_3354_ = v___x_3364_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3369_, lean_object* v___x_3370_, lean_object* v___x_3371_, uint8_t v___x_3372_, lean_object* v___x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_Meta_Cases_cases(v_mvarId_3369_, v___x_3370_, v___x_3371_, v___x_3372_, v___x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3390_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3384_ = lean_array_to_list(v_a_3380_);
v___x_3385_ = lean_box(0);
v___x_3386_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3384_, v___x_3385_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3386_);
v___x_3388_ = v___x_3382_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3379_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3379_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3399_, lean_object* v___x_3400_, lean_object* v___x_3401_, lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
uint8_t v___x_6231__boxed_3409_; lean_object* v_res_3410_; 
v___x_6231__boxed_3409_ = lean_unbox(v___x_3402_);
v_res_3410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3399_, v___x_3400_, v___x_3401_, v___x_6231__boxed_3409_, v___x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3416_, lean_object* v_mvarId_3417_, lean_object* v_as_3418_, size_t v_sz_3419_, size_t v_i_3420_, lean_object* v_b_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_usize_dec_lt(v_i_3420_, v_sz_3419_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec(v_mvarId_3417_);
lean_dec_ref(v_p_3416_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_b_3421_);
return v___x_3428_;
}
else
{
lean_object* v_snd_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3497_; 
v_snd_3429_ = lean_ctor_get(v_b_3421_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_b_3421_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v_b_3421_, 0);
lean_dec(v_unused_3498_);
v___x_3431_ = v_b_3421_;
v_isShared_3432_ = v_isSharedCheck_3497_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_snd_3429_);
lean_dec(v_b_3421_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3497_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v_a_3435_; lean_object* v_a_3442_; 
v___x_3433_ = lean_box(0);
v_a_3442_ = lean_array_uget(v_as_3418_, v_i_3420_);
if (lean_obj_tag(v_a_3442_) == 0)
{
v_a_3435_ = v_snd_3429_;
goto v___jp_3434_;
}
else
{
lean_object* v_val_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3496_; 
v_val_3443_ = lean_ctor_get(v_a_3442_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_a_3442_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3445_ = v_a_3442_;
v_isShared_3446_ = v_isSharedCheck_3496_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_val_3443_);
lean_dec(v_a_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3496_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3416_);
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3424_);
lean_inc(v___y_3423_);
lean_inc_ref(v___y_3422_);
lean_inc(v_val_3443_);
v___x_3449_ = lean_apply_6(v_p_3416_, v_val_3443_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, lean_box(0));
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; uint8_t v___x_3451_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3451_ == 0)
{
lean_del_object(v___x_3445_);
lean_dec(v_val_3443_);
lean_dec(v_snd_3429_);
v_a_3435_ = v___x_3448_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___f_3456_; lean_object* v___x_3457_; 
v___x_3452_ = l_Lean_LocalDecl_fvarId(v_val_3443_);
lean_dec(v_val_3443_);
v___x_3453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3454_ = 0;
v___x_3455_ = lean_box(v___x_3454_);
lean_inc(v_mvarId_3417_);
v___f_3456_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3456_, 0, v_mvarId_3417_);
lean_closure_set(v___f_3456_, 1, v___x_3452_);
lean_closure_set(v___f_3456_, 2, v___x_3453_);
lean_closure_set(v___f_3456_, 3, v___x_3455_);
lean_closure_set(v___f_3456_, 4, v___x_3433_);
v___x_3457_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3456_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3479_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3479_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3479_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
if (lean_obj_tag(v_a_3458_) == 0)
{
lean_del_object(v___x_3460_);
lean_del_object(v___x_3445_);
lean_dec(v_snd_3429_);
v_a_3435_ = v___x_3448_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3463_; 
lean_del_object(v___x_3431_);
lean_dec(v_mvarId_3417_);
lean_dec_ref(v_p_3416_);
lean_inc_ref(v_a_3458_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v_a_3458_);
v___x_3463_ = v___x_3445_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
v_isSharedCheck_3476_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v_a_3458_, 0);
lean_dec(v_unused_3477_);
v___x_3465_ = v_a_3458_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_dec(v_a_3458_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3463_);
lean_ctor_set(v___x_3467_, 1, v___x_3447_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set_tag(v___x_3465_, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_snd_3429_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3471_);
v___x_3473_ = v___x_3460_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_del_object(v___x_3445_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3429_);
lean_dec(v_mvarId_3417_);
lean_dec_ref(v_p_3416_);
v_a_3480_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3457_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3457_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_del_object(v___x_3445_);
lean_dec(v_val_3443_);
lean_del_object(v___x_3431_);
lean_dec(v_snd_3429_);
lean_dec(v_mvarId_3417_);
lean_dec_ref(v_p_3416_);
v_a_3488_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3449_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3449_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3437_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v_a_3435_);
lean_ctor_set(v___x_3431_, 0, v___x_3433_);
v___x_3437_ = v___x_3431_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3435_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
size_t v___x_3438_; size_t v___x_3439_; 
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_add(v_i_3420_, v___x_3438_);
v_i_3420_ = v___x_3439_;
v_b_3421_ = v___x_3437_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3499_, lean_object* v_mvarId_3500_, lean_object* v_as_3501_, lean_object* v_sz_3502_, lean_object* v_i_3503_, lean_object* v_b_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
size_t v_sz_boxed_3510_; size_t v_i_boxed_3511_; lean_object* v_res_3512_; 
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3502_);
lean_dec(v_sz_3502_);
v_i_boxed_3511_ = lean_unbox_usize(v_i_3503_);
lean_dec(v_i_3503_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3499_, v_mvarId_3500_, v_as_3501_, v_sz_boxed_3510_, v_i_boxed_3511_, v_b_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v_as_3501_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3513_, lean_object* v_mvarId_3514_, lean_object* v_as_3515_, size_t v_sz_3516_, size_t v_i_3517_, lean_object* v_b_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_usize_dec_lt(v_i_3517_, v_sz_3516_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
lean_dec(v_mvarId_3514_);
lean_dec_ref(v_p_3513_);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_b_3518_);
return v___x_3525_;
}
else
{
lean_object* v_snd_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3594_; 
v_snd_3526_ = lean_ctor_get(v_b_3518_, 1);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_b_3518_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v_b_3518_, 0);
lean_dec(v_unused_3595_);
v___x_3528_ = v_b_3518_;
v_isShared_3529_ = v_isSharedCheck_3594_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_snd_3526_);
lean_dec(v_b_3518_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3594_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_a_3532_; lean_object* v_a_3539_; 
v___x_3530_ = lean_box(0);
v_a_3539_ = lean_array_uget(v_as_3515_, v_i_3517_);
if (lean_obj_tag(v_a_3539_) == 0)
{
v_a_3532_ = v_snd_3526_;
goto v___jp_3531_;
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3593_; 
v_val_3540_ = lean_ctor_get(v_a_3539_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_a_3539_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3542_ = v_a_3539_;
v_isShared_3543_ = v_isSharedCheck_3593_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_val_3540_);
lean_dec(v_a_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3593_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = lean_box(0);
v___x_3545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3513_);
lean_inc(v___y_3522_);
lean_inc_ref(v___y_3521_);
lean_inc(v___y_3520_);
lean_inc_ref(v___y_3519_);
lean_inc(v_val_3540_);
v___x_3546_ = lean_apply_6(v_p_3513_, v_val_3540_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, lean_box(0));
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; uint8_t v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = lean_unbox(v_a_3547_);
lean_dec(v_a_3547_);
if (v___x_3548_ == 0)
{
lean_del_object(v___x_3542_);
lean_dec(v_val_3540_);
lean_dec(v_snd_3526_);
v_a_3532_ = v___x_3545_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; 
v___x_3549_ = l_Lean_LocalDecl_fvarId(v_val_3540_);
lean_dec(v_val_3540_);
v___x_3550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3551_ = 0;
v___x_3552_ = lean_box(v___x_3551_);
lean_inc(v_mvarId_3514_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3553_, 0, v_mvarId_3514_);
lean_closure_set(v___f_3553_, 1, v___x_3549_);
lean_closure_set(v___f_3553_, 2, v___x_3550_);
lean_closure_set(v___f_3553_, 3, v___x_3552_);
lean_closure_set(v___f_3553_, 4, v___x_3530_);
v___x_3554_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3553_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3576_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3576_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3576_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
if (lean_obj_tag(v_a_3555_) == 0)
{
lean_del_object(v___x_3557_);
lean_del_object(v___x_3542_);
lean_dec(v_snd_3526_);
v_a_3532_ = v___x_3545_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3560_; 
lean_del_object(v___x_3528_);
lean_dec(v_mvarId_3514_);
lean_dec_ref(v_p_3513_);
lean_inc_ref(v_a_3555_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v_a_3555_);
v___x_3560_ = v___x_3542_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3573_; 
v_isSharedCheck_3573_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v_a_3555_, 0);
lean_dec(v_unused_3574_);
v___x_3562_ = v_a_3555_;
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v_a_3555_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3560_);
lean_ctor_set(v___x_3564_, 1, v___x_3544_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set_tag(v___x_3562_, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v_snd_3526_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3568_);
v___x_3570_ = v___x_3557_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3542_);
lean_del_object(v___x_3528_);
lean_dec(v_snd_3526_);
lean_dec(v_mvarId_3514_);
lean_dec_ref(v_p_3513_);
v_a_3577_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3554_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3554_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_del_object(v___x_3542_);
lean_dec(v_val_3540_);
lean_del_object(v___x_3528_);
lean_dec(v_snd_3526_);
lean_dec(v_mvarId_3514_);
lean_dec_ref(v_p_3513_);
v_a_3585_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3546_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3546_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
v___jp_3531_:
{
lean_object* v___x_3534_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_a_3532_);
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3534_ = v___x_3528_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_a_3532_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_add(v_i_3517_, v___x_3535_);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3513_, v_mvarId_3514_, v_as_3515_, v_sz_3516_, v___x_3536_, v___x_3534_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
return v___x_3537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3596_, lean_object* v_mvarId_3597_, lean_object* v_as_3598_, lean_object* v_sz_3599_, lean_object* v_i_3600_, lean_object* v_b_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
size_t v_sz_boxed_3607_; size_t v_i_boxed_3608_; lean_object* v_res_3609_; 
v_sz_boxed_3607_ = lean_unbox_usize(v_sz_3599_);
lean_dec(v_sz_3599_);
v_i_boxed_3608_ = lean_unbox_usize(v_i_3600_);
lean_dec(v_i_3600_);
v_res_3609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3596_, v_mvarId_3597_, v_as_3598_, v_sz_boxed_3607_, v_i_boxed_3608_, v_b_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_as_3598_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3610_, lean_object* v_p_3611_, lean_object* v_mvarId_3612_, lean_object* v_n_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
if (lean_obj_tag(v_n_3613_) == 0)
{
lean_object* v_cs_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; size_t v_sz_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
v_cs_3620_ = lean_ctor_get(v_n_3613_, 0);
v___x_3621_ = lean_box(0);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v_b_3614_);
v_sz_3623_ = lean_array_size(v_cs_3620_);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3610_, v_p_3611_, v_mvarId_3612_, v_cs_3620_, v_sz_3623_, v___x_3624_, v___x_3622_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3640_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3640_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3640_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v_fst_3630_; 
v_fst_3630_ = lean_ctor_get(v_a_3626_, 0);
if (lean_obj_tag(v_fst_3630_) == 0)
{
lean_object* v_snd_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
v_snd_3631_ = lean_ctor_get(v_a_3626_, 1);
lean_inc(v_snd_3631_);
lean_dec(v_a_3626_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_snd_3631_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3632_);
v___x_3634_ = v___x_3628_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
else
{
lean_object* v_val_3636_; lean_object* v___x_3638_; 
lean_inc_ref(v_fst_3630_);
lean_dec(v_a_3626_);
v_val_3636_ = lean_ctor_get(v_fst_3630_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_fst_3630_, 1);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v_val_3636_);
v___x_3638_ = v___x_3628_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_val_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
v_a_3641_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3625_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3625_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
lean_object* v_vs_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; size_t v_sz_3652_; size_t v___x_3653_; lean_object* v___x_3654_; 
v_vs_3649_ = lean_ctor_get(v_n_3613_, 0);
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
lean_ctor_set(v___x_3651_, 1, v_b_3614_);
v_sz_3652_ = lean_array_size(v_vs_3649_);
v___x_3653_ = ((size_t)0ULL);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3611_, v_mvarId_3612_, v_vs_3649_, v_sz_3652_, v___x_3653_, v___x_3651_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3669_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_fst_3659_; 
v_fst_3659_ = lean_ctor_get(v_a_3655_, 0);
if (lean_obj_tag(v_fst_3659_) == 0)
{
lean_object* v_snd_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
v_snd_3660_ = lean_ctor_get(v_a_3655_, 1);
lean_inc(v_snd_3660_);
lean_dec(v_a_3655_);
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_snd_3660_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3661_);
v___x_3663_ = v___x_3657_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
lean_object* v_val_3665_; lean_object* v___x_3667_; 
lean_inc_ref(v_fst_3659_);
lean_dec(v_a_3655_);
v_val_3665_ = lean_ctor_get(v_fst_3659_, 0);
lean_inc(v_val_3665_);
lean_dec_ref_known(v_fst_3659_, 1);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v_val_3665_);
v___x_3667_ = v___x_3657_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_val_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3654_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3654_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3678_, lean_object* v_p_3679_, lean_object* v_mvarId_3680_, lean_object* v_as_3681_, size_t v_sz_3682_, size_t v_i_3683_, lean_object* v_b_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_usize_dec_lt(v_i_3683_, v_sz_3682_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; 
lean_dec(v_mvarId_3680_);
lean_dec_ref(v_p_3679_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_b_3684_);
return v___x_3691_;
}
else
{
lean_object* v_snd_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3726_; 
v_snd_3692_ = lean_ctor_get(v_b_3684_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_b_3684_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v_b_3684_, 0);
lean_dec(v_unused_3727_);
v___x_3694_ = v_b_3684_;
v_isShared_3695_ = v_isSharedCheck_3726_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_snd_3692_);
lean_dec(v_b_3684_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3726_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v_a_3697_; lean_object* v___x_3698_; 
v___x_3696_ = lean_box(0);
v_a_3697_ = lean_array_uget_borrowed(v_as_3681_, v_i_3683_);
lean_inc(v_snd_3692_);
lean_inc(v_mvarId_3680_);
lean_inc_ref(v_p_3679_);
v___x_3698_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3678_, v_p_3679_, v_mvarId_3680_, v_a_3697_, v_snd_3692_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3717_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3717_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3717_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
if (lean_obj_tag(v_a_3699_) == 0)
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
lean_dec(v_mvarId_3680_);
lean_dec_ref(v_p_3679_);
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v_a_3699_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3703_);
v___x_3705_ = v___x_3694_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_snd_3692_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3705_);
v___x_3707_ = v___x_3701_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; 
lean_del_object(v___x_3701_);
lean_dec(v_snd_3692_);
v_a_3710_ = lean_ctor_get(v_a_3699_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v_a_3699_, 1);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v_a_3710_);
lean_ctor_set(v___x_3694_, 0, v___x_3696_);
v___x_3712_ = v___x_3694_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3710_);
v___x_3712_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
size_t v___x_3713_; size_t v___x_3714_; 
v___x_3713_ = ((size_t)1ULL);
v___x_3714_ = lean_usize_add(v_i_3683_, v___x_3713_);
v_i_3683_ = v___x_3714_;
v_b_3684_ = v___x_3712_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3694_);
lean_dec(v_snd_3692_);
lean_dec(v_mvarId_3680_);
lean_dec_ref(v_p_3679_);
v_a_3718_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3698_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3698_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3728_, lean_object* v_p_3729_, lean_object* v_mvarId_3730_, lean_object* v_as_3731_, lean_object* v_sz_3732_, lean_object* v_i_3733_, lean_object* v_b_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
size_t v_sz_boxed_3740_; size_t v_i_boxed_3741_; lean_object* v_res_3742_; 
v_sz_boxed_3740_ = lean_unbox_usize(v_sz_3732_);
lean_dec(v_sz_3732_);
v_i_boxed_3741_ = lean_unbox_usize(v_i_3733_);
lean_dec(v_i_3733_);
v_res_3742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3728_, v_p_3729_, v_mvarId_3730_, v_as_3731_, v_sz_boxed_3740_, v_i_boxed_3741_, v_b_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v_as_3731_);
lean_dec_ref(v_init_3728_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3743_, lean_object* v_p_3744_, lean_object* v_mvarId_3745_, lean_object* v_n_3746_, lean_object* v_b_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3743_, v_p_3744_, v_mvarId_3745_, v_n_3746_, v_b_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec_ref(v_n_3746_);
lean_dec_ref(v_init_3743_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3757_, lean_object* v_mvarId_3758_, lean_object* v_as_3759_, size_t v_sz_3760_, size_t v_i_3761_, lean_object* v_b_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v___x_3768_; 
v___x_3768_ = lean_usize_dec_lt(v_i_3761_, v_sz_3760_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; 
lean_dec(v_mvarId_3758_);
lean_dec_ref(v_p_3757_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v_b_3762_);
return v___x_3769_;
}
else
{
lean_object* v_snd_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3837_; 
v_snd_3770_ = lean_ctor_get(v_b_3762_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_b_3762_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_b_3762_, 0);
lean_dec(v_unused_3838_);
v___x_3772_ = v_b_3762_;
v_isShared_3773_ = v_isSharedCheck_3837_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_snd_3770_);
lean_dec(v_b_3762_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3837_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v_a_3776_; lean_object* v_a_3783_; 
v___x_3774_ = lean_box(0);
v_a_3783_ = lean_array_uget(v_as_3759_, v_i_3761_);
if (lean_obj_tag(v_a_3783_) == 0)
{
v_a_3776_ = v_snd_3770_;
goto v___jp_3775_;
}
else
{
lean_object* v_val_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3836_; 
v_val_3784_ = lean_ctor_get(v_a_3783_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3786_ = v_a_3783_;
v_isShared_3787_ = v_isSharedCheck_3836_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_val_3784_);
lean_dec(v_a_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3836_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3788_ = lean_box(0);
v___x_3789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3757_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
lean_inc(v_val_3784_);
v___x_3790_ = lean_apply_6(v_p_3757_, v_val_3784_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, lean_box(0));
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; uint8_t v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3792_ = lean_unbox(v_a_3791_);
lean_dec(v_a_3791_);
if (v___x_3792_ == 0)
{
lean_del_object(v___x_3786_);
lean_dec(v_val_3784_);
lean_dec(v_snd_3770_);
v_a_3776_ = v___x_3789_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___f_3797_; lean_object* v___x_3798_; 
v___x_3793_ = l_Lean_LocalDecl_fvarId(v_val_3784_);
lean_dec(v_val_3784_);
v___x_3794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3795_ = 0;
v___x_3796_ = lean_box(v___x_3795_);
lean_inc(v_mvarId_3758_);
v___f_3797_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3797_, 0, v_mvarId_3758_);
lean_closure_set(v___f_3797_, 1, v___x_3793_);
lean_closure_set(v___f_3797_, 2, v___x_3794_);
lean_closure_set(v___f_3797_, 3, v___x_3796_);
lean_closure_set(v___f_3797_, 4, v___x_3774_);
v___x_3798_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3797_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3819_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3819_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3819_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
if (lean_obj_tag(v_a_3799_) == 0)
{
lean_del_object(v___x_3801_);
lean_del_object(v___x_3786_);
lean_dec(v_snd_3770_);
v_a_3776_ = v___x_3789_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3804_; 
lean_del_object(v___x_3772_);
lean_dec(v_mvarId_3758_);
lean_dec_ref(v_p_3757_);
lean_inc_ref(v_a_3799_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v_a_3799_);
v___x_3804_ = v___x_3786_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3816_; 
v_isSharedCheck_3816_ = !lean_is_exclusive(v_a_3799_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v_a_3799_, 0);
lean_dec(v_unused_3817_);
v___x_3806_ = v_a_3799_;
v_isShared_3807_ = v_isSharedCheck_3816_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v_a_3799_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3816_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3804_);
lean_ctor_set(v___x_3808_, 1, v___x_3788_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
lean_ctor_set(v___x_3811_, 1, v_snd_3770_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3811_);
v___x_3813_ = v___x_3801_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_del_object(v___x_3786_);
lean_del_object(v___x_3772_);
lean_dec(v_snd_3770_);
lean_dec(v_mvarId_3758_);
lean_dec_ref(v_p_3757_);
v_a_3820_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3798_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3798_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3786_);
lean_dec(v_val_3784_);
lean_del_object(v___x_3772_);
lean_dec(v_snd_3770_);
lean_dec(v_mvarId_3758_);
lean_dec_ref(v_p_3757_);
v_a_3828_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3790_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3790_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
v___jp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_a_3776_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3778_ = v___x_3772_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_a_3776_);
v___x_3778_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
size_t v___x_3779_; size_t v___x_3780_; 
v___x_3779_ = ((size_t)1ULL);
v___x_3780_ = lean_usize_add(v_i_3761_, v___x_3779_);
v_i_3761_ = v___x_3780_;
v_b_3762_ = v___x_3778_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3839_, lean_object* v_mvarId_3840_, lean_object* v_as_3841_, lean_object* v_sz_3842_, lean_object* v_i_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
size_t v_sz_boxed_3850_; size_t v_i_boxed_3851_; lean_object* v_res_3852_; 
v_sz_boxed_3850_ = lean_unbox_usize(v_sz_3842_);
lean_dec(v_sz_3842_);
v_i_boxed_3851_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_res_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3839_, v_mvarId_3840_, v_as_3841_, v_sz_boxed_3850_, v_i_boxed_3851_, v_b_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v_as_3841_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3853_, lean_object* v_mvarId_3854_, lean_object* v_as_3855_, size_t v_sz_3856_, size_t v_i_3857_, lean_object* v_b_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3857_, v_sz_3856_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
lean_dec(v_mvarId_3854_);
lean_dec_ref(v_p_3853_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_b_3858_);
return v___x_3865_;
}
else
{
lean_object* v_snd_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3933_; 
v_snd_3866_ = lean_ctor_get(v_b_3858_, 1);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_b_3858_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v_b_3858_, 0);
lean_dec(v_unused_3934_);
v___x_3868_ = v_b_3858_;
v_isShared_3869_ = v_isSharedCheck_3933_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_snd_3866_);
lean_dec(v_b_3858_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3933_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v_a_3872_; lean_object* v_a_3879_; 
v___x_3870_ = lean_box(0);
v_a_3879_ = lean_array_uget(v_as_3855_, v_i_3857_);
if (lean_obj_tag(v_a_3879_) == 0)
{
v_a_3872_ = v_snd_3866_;
goto v___jp_3871_;
}
else
{
lean_object* v_val_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3932_; 
v_val_3880_ = lean_ctor_get(v_a_3879_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3882_ = v_a_3879_;
v_isShared_3883_ = v_isSharedCheck_3932_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_val_3880_);
lean_dec(v_a_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3932_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_box(0);
v___x_3885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3853_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v_val_3880_);
v___x_3886_ = lean_apply_6(v_p_3853_, v_val_3880_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, lean_box(0));
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; uint8_t v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_unbox(v_a_3887_);
lean_dec(v_a_3887_);
if (v___x_3888_ == 0)
{
lean_del_object(v___x_3882_);
lean_dec(v_val_3880_);
lean_dec(v_snd_3866_);
v_a_3872_ = v___x_3885_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___f_3893_; lean_object* v___x_3894_; 
v___x_3889_ = l_Lean_LocalDecl_fvarId(v_val_3880_);
lean_dec(v_val_3880_);
v___x_3890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3891_ = 0;
v___x_3892_ = lean_box(v___x_3891_);
lean_inc(v_mvarId_3854_);
v___f_3893_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3893_, 0, v_mvarId_3854_);
lean_closure_set(v___f_3893_, 1, v___x_3889_);
lean_closure_set(v___f_3893_, 2, v___x_3890_);
lean_closure_set(v___f_3893_, 3, v___x_3892_);
lean_closure_set(v___f_3893_, 4, v___x_3870_);
v___x_3894_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3893_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3915_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3915_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3915_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
if (lean_obj_tag(v_a_3895_) == 0)
{
lean_del_object(v___x_3897_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3866_);
v_a_3872_ = v___x_3885_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3900_; 
lean_del_object(v___x_3868_);
lean_dec(v_mvarId_3854_);
lean_dec_ref(v_p_3853_);
lean_inc_ref(v_a_3895_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v_a_3895_);
v___x_3900_ = v___x_3882_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3912_; 
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3895_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; 
v_unused_3913_ = lean_ctor_get(v_a_3895_, 0);
lean_dec(v_unused_3913_);
v___x_3902_ = v_a_3895_;
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
else
{
lean_dec(v_a_3895_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3900_);
lean_ctor_set(v___x_3904_, 1, v___x_3884_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
lean_ctor_set(v___x_3907_, 1, v_snd_3866_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3907_);
v___x_3909_ = v___x_3897_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_del_object(v___x_3882_);
lean_del_object(v___x_3868_);
lean_dec(v_snd_3866_);
lean_dec(v_mvarId_3854_);
lean_dec_ref(v_p_3853_);
v_a_3916_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3894_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3894_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
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
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_del_object(v___x_3882_);
lean_dec(v_val_3880_);
lean_del_object(v___x_3868_);
lean_dec(v_snd_3866_);
lean_dec(v_mvarId_3854_);
lean_dec_ref(v_p_3853_);
v_a_3924_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3886_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3886_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
v___jp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v_a_3872_);
lean_ctor_set(v___x_3868_, 0, v___x_3870_);
v___x_3874_ = v___x_3868_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_a_3872_);
v___x_3874_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = ((size_t)1ULL);
v___x_3876_ = lean_usize_add(v_i_3857_, v___x_3875_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3853_, v_mvarId_3854_, v_as_3855_, v_sz_3856_, v___x_3876_, v___x_3874_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3935_, lean_object* v_mvarId_3936_, lean_object* v_as_3937_, lean_object* v_sz_3938_, lean_object* v_i_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
size_t v_sz_boxed_3946_; size_t v_i_boxed_3947_; lean_object* v_res_3948_; 
v_sz_boxed_3946_ = lean_unbox_usize(v_sz_3938_);
lean_dec(v_sz_3938_);
v_i_boxed_3947_ = lean_unbox_usize(v_i_3939_);
lean_dec(v_i_3939_);
v_res_3948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3935_, v_mvarId_3936_, v_as_3937_, v_sz_boxed_3946_, v_i_boxed_3947_, v_b_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec_ref(v_as_3937_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3949_, lean_object* v_mvarId_3950_, lean_object* v_t_3951_, lean_object* v_init_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_root_3958_; lean_object* v_tail_3959_; lean_object* v___x_3960_; 
v_root_3958_ = lean_ctor_get(v_t_3951_, 0);
v_tail_3959_ = lean_ctor_get(v_t_3951_, 1);
lean_inc(v_mvarId_3950_);
lean_inc_ref(v_p_3949_);
lean_inc_ref(v_init_3952_);
v___x_3960_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3952_, v_p_3949_, v_mvarId_3950_, v_root_3958_, v_init_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec_ref(v_init_3952_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3997_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3997_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3997_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
if (lean_obj_tag(v_a_3961_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; 
lean_dec(v_mvarId_3950_);
lean_dec_ref(v_p_3949_);
v_a_3965_ = lean_ctor_get(v_a_3961_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v_a_3961_, 1);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v_a_3965_);
v___x_3967_ = v___x_3963_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3965_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
lean_del_object(v___x_3963_);
v_a_3969_ = lean_ctor_get(v_a_3961_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v_a_3961_, 1);
v___x_3970_ = lean_box(0);
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
lean_ctor_set(v___x_3971_, 1, v_a_3969_);
v_sz_3972_ = lean_array_size(v_tail_3959_);
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3949_, v_mvarId_3950_, v_tail_3959_, v_sz_3972_, v___x_3973_, v___x_3971_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3988_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_fst_3979_; 
v_fst_3979_ = lean_ctor_get(v_a_3975_, 0);
if (lean_obj_tag(v_fst_3979_) == 0)
{
lean_object* v_snd_3980_; lean_object* v___x_3982_; 
v_snd_3980_ = lean_ctor_get(v_a_3975_, 1);
lean_inc(v_snd_3980_);
lean_dec(v_a_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_snd_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_snd_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
else
{
lean_object* v_val_3984_; lean_object* v___x_3986_; 
lean_inc_ref(v_fst_3979_);
lean_dec(v_a_3975_);
v_val_3984_ = lean_ctor_get(v_fst_3979_, 0);
lean_inc(v_val_3984_);
lean_dec_ref_known(v_fst_3979_, 1);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_val_3984_);
v___x_3986_ = v___x_3977_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_val_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3974_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3974_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_mvarId_3950_);
lean_dec_ref(v_p_3949_);
v_a_3998_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3960_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3960_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4006_, lean_object* v_mvarId_4007_, lean_object* v_t_4008_, lean_object* v_init_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4006_, v_mvarId_4007_, v_t_4008_, v_init_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec_ref(v_t_4008_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4019_, lean_object* v_mvarId_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_lctx_4026_; lean_object* v_decls_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_lctx_4026_ = lean_ctor_get(v___y_4021_, 2);
v_decls_4027_ = lean_ctor_get(v_lctx_4026_, 1);
v___x_4028_ = lean_box(0);
v___x_4029_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4030_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4019_, v_mvarId_4020_, v_decls_4027_, v___x_4029_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4043_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4043_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4043_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v_fst_4035_; 
v_fst_4035_ = lean_ctor_get(v_a_4031_, 0);
lean_inc(v_fst_4035_);
lean_dec(v_a_4031_);
if (lean_obj_tag(v_fst_4035_) == 0)
{
lean_object* v___x_4037_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4028_);
v___x_4037_ = v___x_4033_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4028_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
else
{
lean_object* v_val_4039_; lean_object* v___x_4041_; 
v_val_4039_ = lean_ctor_get(v_fst_4035_, 0);
lean_inc(v_val_4039_);
lean_dec_ref_known(v_fst_4035_, 1);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v_val_4039_);
v___x_4041_ = v___x_4033_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_val_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4030_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4030_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4052_, lean_object* v_mvarId_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_MVarId_casesRec___lam__0(v_p_4052_, v_mvarId_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4060_, lean_object* v_mvarId_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___f_4067_; lean_object* v___x_4068_; 
lean_inc(v_mvarId_4061_);
v___f_4067_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4067_, 0, v_p_4060_);
lean_closure_set(v___f_4067_, 1, v_mvarId_4061_);
v___x_4068_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4061_, v___f_4067_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4069_, lean_object* v_mvarId_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_MVarId_casesRec___lam__1(v_p_4069_, v_mvarId_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4077_, lean_object* v_p_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v___f_4084_; lean_object* v___x_4085_; 
v___f_4084_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4084_, 0, v_p_4078_);
v___x_4085_ = l_Lean_Meta_saturate(v_mvarId_4077_, v___f_4084_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4086_, lean_object* v_p_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_MVarId_casesRec(v_mvarId_4086_, v_p_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4094_, lean_object* v___y_4095_){
_start:
{
uint8_t v___x_4097_; 
v___x_4097_ = l_Lean_Expr_hasMVar(v_e_4094_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_e_4094_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; lean_object* v_mctx_4100_; lean_object* v___x_4101_; lean_object* v_fst_4102_; lean_object* v_snd_4103_; lean_object* v___x_4104_; lean_object* v_cache_4105_; lean_object* v_zetaDeltaFVarIds_4106_; lean_object* v_postponed_4107_; lean_object* v_diag_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4117_; 
v___x_4099_ = lean_st_ref_get(v___y_4095_);
v_mctx_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc_ref(v_mctx_4100_);
lean_dec(v___x_4099_);
v___x_4101_ = l_Lean_instantiateMVarsCore(v_mctx_4100_, v_e_4094_);
v_fst_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_fst_4102_);
v_snd_4103_ = lean_ctor_get(v___x_4101_, 1);
lean_inc(v_snd_4103_);
lean_dec_ref(v___x_4101_);
v___x_4104_ = lean_st_ref_take(v___y_4095_);
v_cache_4105_ = lean_ctor_get(v___x_4104_, 1);
v_zetaDeltaFVarIds_4106_ = lean_ctor_get(v___x_4104_, 2);
v_postponed_4107_ = lean_ctor_get(v___x_4104_, 3);
v_diag_4108_ = lean_ctor_get(v___x_4104_, 4);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; 
v_unused_4118_ = lean_ctor_get(v___x_4104_, 0);
lean_dec(v_unused_4118_);
v___x_4110_ = v___x_4104_;
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_diag_4108_);
lean_inc(v_postponed_4107_);
lean_inc(v_zetaDeltaFVarIds_4106_);
lean_inc(v_cache_4105_);
lean_dec(v___x_4104_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4117_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v_snd_4103_);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_snd_4103_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_cache_4105_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_zetaDeltaFVarIds_4106_);
lean_ctor_set(v_reuseFailAlloc_4116_, 3, v_postponed_4107_);
lean_ctor_set(v_reuseFailAlloc_4116_, 4, v_diag_4108_);
v___x_4113_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = lean_st_ref_put(v___y_4095_, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_fst_4102_);
return v___x_4115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4119_, v___y_4120_);
lean_dec(v___y_4120_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4123_, v___y_4125_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4159_; 
v___x_4146_ = l_Lean_LocalDecl_type(v_localDecl_4140_);
v___x_4147_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4146_, v___y_4142_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4159_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4159_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4152_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4153_ = lean_unsigned_to_nat(2u);
v___x_4154_ = l_Lean_Expr_isAppOfArity(v_a_4148_, v___x_4152_, v___x_4153_);
lean_dec(v_a_4148_);
v___x_4155_ = lean_box(v___x_4154_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4155_);
v___x_4157_ = v___x_4150_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec_ref(v_localDecl_4160_);
return v_res_4166_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4172_ = l_Lean_MessageData_ofFormat(v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; 
v___f_4179_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4180_ = l_Lean_MVarId_casesRec(v_mvarId_4173_, v___f_4179_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v___x_4182_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4183_ = l_Lean_Meta_exactlyOne(v_a_4181_, v___x_4182_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
lean_dec(v_a_4181_);
return v___x_4183_;
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
v_a_4184_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4180_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4180_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_MVarId_casesAnd(v_mvarId_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4221_; 
v___x_4205_ = l_Lean_LocalDecl_type(v_localDecl_4199_);
v___x_4206_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4205_, v___y_4201_);
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
uint8_t v___x_4211_; 
v___x_4211_ = l_Lean_Expr_isEq(v_a_4207_);
if (v___x_4211_ == 0)
{
uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4212_ = l_Lean_Expr_isHEq(v_a_4207_);
lean_dec(v_a_4207_);
v___x_4213_ = lean_box(v___x_4212_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4213_);
v___x_4215_ = v___x_4209_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
lean_dec(v_a_4207_);
v___x_4217_ = lean_box(v___x_4211_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v_localDecl_4222_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___f_4236_; lean_object* v___x_4237_; 
v___f_4236_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4237_ = l_Lean_MVarId_casesRec(v_mvarId_4230_, v___f_4236_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___x_4239_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4240_ = l_Lean_Meta_ensureAtMostOne(v_a_4238_, v___x_4239_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
lean_dec(v_a_4238_);
return v___x_4240_;
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
v_a_4241_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4237_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4237_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_MVarId_substEqs(v_mvarId_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4256_, lean_object* v_tag_4257_, lean_object* v_hyp_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4256_, v_tag_4257_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; uint8_t v___x_4270_; uint8_t v___x_4271_; lean_object* v___x_4272_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc_n(v_a_4265_, 2);
lean_dec_ref_known(v___x_4264_, 1);
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = lean_mk_empty_array_with_capacity(v___x_4266_);
lean_inc_ref(v_hyp_4258_);
v___x_4268_ = lean_array_push(v___x_4267_, v_hyp_4258_);
v___x_4269_ = 0;
v___x_4270_ = 1;
v___x_4271_ = 1;
v___x_4272_ = l_Lean_Meta_mkLambdaFVars(v___x_4268_, v_a_4265_, v___x_4269_, v___x_4270_, v___x_4269_, v___x_4270_, v___x_4271_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec_ref(v___x_4268_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4284_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4275_ = v___x_4272_;
v_isShared_4276_ = v_isSharedCheck_4284_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4284_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4277_ = l_Lean_Expr_mvarId_x21(v_a_4265_);
lean_dec(v_a_4265_);
v___x_4278_ = l_Lean_Expr_fvarId_x21(v_hyp_4258_);
lean_dec_ref(v_hyp_4258_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4280_, 0, v_a_4273_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 0, v___x_4280_);
v___x_4282_ = v___x_4275_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v_a_4265_);
lean_dec_ref(v_hyp_4258_);
v_a_4285_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4272_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4272_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v_hyp_4258_);
v_a_4293_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4264_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4264_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4301_, lean_object* v_tag_4302_, lean_object* v_hyp_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4301_, v_tag_4302_, v_hyp_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4310_, lean_object* v_hName_4311_, lean_object* v_goalType_4312_, lean_object* v_tag_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v___f_4319_; lean_object* v___x_4320_; 
v___f_4319_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4319_, 0, v_goalType_4312_);
lean_closure_set(v___f_4319_, 1, v_tag_4313_);
v___x_4320_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4311_, v_p_4310_, v___f_4319_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4321_, lean_object* v_hName_4322_, lean_object* v_goalType_4323_, lean_object* v_tag_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4321_, v_hName_4322_, v_goalType_4323_, v_tag_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
return v_res_4330_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = lean_box(0);
v___x_4343_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4344_ = l_Lean_Expr_const___override(v___x_4343_, v___x_4342_);
return v___x_4344_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
return v___x_4349_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4352_, lean_object* v_p_4353_, lean_object* v_hName_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v_mvarId_4352_);
v___x_4360_ = l_Lean_MVarId_getType(v_mvarId_4352_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
lean_inc(v_mvarId_4352_);
v___x_4362_ = l_Lean_MVarId_getTag(v_mvarId_4352_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___x_4416_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
lean_inc(v_a_4361_);
v___x_4416_ = l_Lean_Meta_isProp(v_a_4361_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; uint8_t v___x_4418_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4416_, 1);
v___x_4418_ = lean_unbox(v_a_4417_);
lean_dec(v_a_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4419_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4420_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4352_);
v___x_4421_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4419_, v_mvarId_4352_, v___x_4420_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_dec_ref_known(v___x_4421_, 1);
v___y_4365_ = v___y_4355_;
v___y_4366_ = v___y_4356_;
v___y_4367_ = v___y_4357_;
v___y_4368_ = v___y_4358_;
goto v___jp_4364_;
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_a_4363_);
lean_dec(v_a_4361_);
lean_dec(v_hName_4354_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
v___y_4365_ = v___y_4355_;
v___y_4366_ = v___y_4356_;
v___y_4367_ = v___y_4357_;
v___y_4368_ = v___y_4358_;
goto v___jp_4364_;
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4363_);
lean_dec(v_a_4361_);
lean_dec(v_hName_4354_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4430_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4416_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4416_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
v___jp_4364_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4363_);
v___x_4370_ = l_Lean_Name_append(v_a_4363_, v___x_4369_);
lean_inc(v_a_4361_);
lean_inc(v_hName_4354_);
lean_inc_ref(v_p_4353_);
v___x_4371_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4353_, v_hName_4354_, v_a_4361_, v___x_4370_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v_fst_4373_; lean_object* v_snd_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v_fst_4373_ = lean_ctor_get(v_a_4372_, 0);
lean_inc(v_fst_4373_);
v_snd_4374_ = lean_ctor_get(v_a_4372_, 1);
lean_inc(v_snd_4374_);
lean_dec(v_a_4372_);
lean_inc_ref(v_p_4353_);
v___x_4375_ = l_Lean_mkNot(v_p_4353_);
v___x_4376_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4377_ = l_Lean_Name_append(v_a_4363_, v___x_4376_);
lean_inc(v_a_4361_);
v___x_4378_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4375_, v_hName_4354_, v_a_4361_, v___x_4377_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v_fst_4380_; lean_object* v_snd_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4399_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
v_fst_4380_ = lean_ctor_get(v_a_4379_, 0);
v_snd_4381_ = lean_ctor_get(v_a_4379_, 1);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_a_4379_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4383_ = v_a_4379_;
v_isShared_4384_ = v_isSharedCheck_4399_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_snd_4381_);
lean_inc(v_fst_4380_);
lean_dec(v_a_4379_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4399_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4397_; 
v___x_4385_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4386_ = l_Lean_mkApp4(v___x_4385_, v_p_4353_, v_a_4361_, v_fst_4373_, v_fst_4380_);
v___x_4387_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4352_, v___x_4386_, v___y_4366_);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v___x_4387_, 0);
lean_dec(v_unused_4398_);
v___x_4389_ = v___x_4387_;
v_isShared_4390_ = v_isSharedCheck_4397_;
goto v_resetjp_4388_;
}
else
{
lean_dec(v___x_4387_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4397_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v_snd_4374_);
v___x_4392_ = v___x_4383_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_snd_4374_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_snd_4381_);
v___x_4392_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
lean_object* v___x_4394_; 
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 0, v___x_4392_);
v___x_4394_ = v___x_4389_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4392_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_snd_4374_);
lean_dec(v_fst_4373_);
lean_dec(v_a_4361_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4400_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4378_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4378_);
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
lean_dec(v_a_4363_);
lean_dec(v_a_4361_);
lean_dec(v_hName_4354_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4408_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4371_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4371_);
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
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_a_4361_);
lean_dec(v_hName_4354_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4438_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4362_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4362_);
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
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_hName_4354_);
lean_dec_ref(v_p_4353_);
lean_dec(v_mvarId_4352_);
v_a_4446_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4360_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4360_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4454_, lean_object* v_p_4455_, lean_object* v_hName_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4454_, v_p_4455_, v_hName_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4463_, lean_object* v_p_4464_, lean_object* v_hName_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v___f_4471_; lean_object* v___x_4472_; 
lean_inc(v_mvarId_4463_);
v___f_4471_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4471_, 0, v_mvarId_4463_);
lean_closure_set(v___f_4471_, 1, v_p_4464_);
lean_closure_set(v___f_4471_, 2, v_hName_4465_);
v___x_4472_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4463_, v___f_4471_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4473_, lean_object* v_p_4474_, lean_object* v_hName_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_MVarId_byCases(v_mvarId_4473_, v_p_4474_, v_hName_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4485_, lean_object* v_p_4486_, lean_object* v_hName_4487_, lean_object* v_dec_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
lean_inc(v_mvarId_4485_);
v___x_4494_ = l_Lean_MVarId_getType(v_mvarId_4485_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4496_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
lean_inc(v_mvarId_4485_);
v___x_4496_ = l_Lean_MVarId_getTag(v_mvarId_4485_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4498_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
lean_inc(v_a_4495_);
v___x_4498_ = l_Lean_Meta_getLevel(v_a_4495_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4497_);
v___x_4501_ = l_Lean_Name_append(v_a_4497_, v___x_4500_);
lean_inc(v_a_4495_);
lean_inc(v_hName_4487_);
lean_inc_ref(v_p_4486_);
v___x_4502_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4486_, v_hName_4487_, v_a_4495_, v___x_4501_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v_fst_4504_; lean_object* v_snd_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4547_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4502_, 1);
v_fst_4504_ = lean_ctor_get(v_a_4503_, 0);
v_snd_4505_ = lean_ctor_get(v_a_4503_, 1);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_a_4503_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4507_ = v_a_4503_;
v_isShared_4508_ = v_isSharedCheck_4547_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_snd_4505_);
lean_inc(v_fst_4504_);
lean_dec(v_a_4503_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4547_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_inc_ref(v_p_4486_);
v___x_4509_ = l_Lean_mkNot(v_p_4486_);
v___x_4510_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4511_ = l_Lean_Name_append(v_a_4497_, v___x_4510_);
lean_inc(v_a_4495_);
v___x_4512_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4509_, v_hName_4487_, v_a_4495_, v___x_4511_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v_fst_4514_; lean_object* v_snd_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4538_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
v_fst_4514_ = lean_ctor_get(v_a_4513_, 0);
v_snd_4515_ = lean_ctor_get(v_a_4513_, 1);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_a_4513_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4517_ = v_a_4513_;
v_isShared_4518_ = v_isSharedCheck_4538_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_snd_4515_);
lean_inc(v_fst_4514_);
lean_dec(v_a_4513_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4538_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4519_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4520_ = lean_box(0);
if (v_isShared_4508_ == 0)
{
lean_ctor_set_tag(v___x_4507_, 1);
lean_ctor_set(v___x_4507_, 1, v___x_4520_);
lean_ctor_set(v___x_4507_, 0, v_a_4499_);
v___x_4522_ = v___x_4507_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4499_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4535_; 
v___x_4523_ = l_Lean_Expr_const___override(v___x_4519_, v___x_4522_);
v___x_4524_ = l_Lean_mkApp5(v___x_4523_, v_a_4495_, v_p_4486_, v_dec_4488_, v_fst_4504_, v_fst_4514_);
v___x_4525_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4485_, v___x_4524_, v___y_4490_);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4535_ == 0)
{
lean_object* v_unused_4536_; 
v_unused_4536_ = lean_ctor_get(v___x_4525_, 0);
lean_dec(v_unused_4536_);
v___x_4527_ = v___x_4525_;
v_isShared_4528_ = v_isSharedCheck_4535_;
goto v_resetjp_4526_;
}
else
{
lean_dec(v___x_4525_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4535_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v_snd_4505_);
v___x_4530_ = v___x_4517_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_snd_4505_);
lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_snd_4515_);
v___x_4530_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4532_; 
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4530_);
v___x_4532_ = v___x_4527_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
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
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_del_object(v___x_4507_);
lean_dec(v_snd_4505_);
lean_dec(v_fst_4504_);
lean_dec(v_a_4499_);
lean_dec(v_a_4495_);
lean_dec_ref(v_dec_4488_);
lean_dec_ref(v_p_4486_);
lean_dec(v_mvarId_4485_);
v_a_4539_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4512_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4512_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_dec(v_a_4499_);
lean_dec(v_a_4497_);
lean_dec(v_a_4495_);
lean_dec_ref(v_dec_4488_);
lean_dec(v_hName_4487_);
lean_dec_ref(v_p_4486_);
lean_dec(v_mvarId_4485_);
v_a_4548_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4502_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4502_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v_a_4497_);
lean_dec(v_a_4495_);
lean_dec_ref(v_dec_4488_);
lean_dec(v_hName_4487_);
lean_dec_ref(v_p_4486_);
lean_dec(v_mvarId_4485_);
v_a_4556_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4498_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4498_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_a_4495_);
lean_dec_ref(v_dec_4488_);
lean_dec(v_hName_4487_);
lean_dec_ref(v_p_4486_);
lean_dec(v_mvarId_4485_);
v_a_4564_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4496_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4496_);
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
lean_dec_ref(v_dec_4488_);
lean_dec(v_hName_4487_);
lean_dec_ref(v_p_4486_);
lean_dec(v_mvarId_4485_);
v_a_4572_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4494_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4494_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4580_, lean_object* v_p_4581_, lean_object* v_hName_4582_, lean_object* v_dec_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4580_, v_p_4581_, v_hName_4582_, v_dec_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4590_, lean_object* v_p_4591_, lean_object* v_dec_4592_, lean_object* v_hName_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___f_4599_; lean_object* v___x_4600_; 
lean_inc(v_mvarId_4590_);
v___f_4599_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4599_, 0, v_mvarId_4590_);
lean_closure_set(v___f_4599_, 1, v_p_4591_);
lean_closure_set(v___f_4599_, 2, v_hName_4593_);
lean_closure_set(v___f_4599_, 3, v_dec_4592_);
v___x_4600_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4590_, v___f_4599_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4601_, lean_object* v_p_4602_, lean_object* v_dec_4603_, lean_object* v_hName_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lean_MVarId_byCasesDec(v_mvarId_4601_, v_p_4602_, v_dec_4603_, v_hName_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
return v_res_4610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = lean_unsigned_to_nat(4241171151u);
v___x_4663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4664_ = l_Lean_Name_num___override(v___x_4663_, v___x_4662_);
return v___x_4664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4668_ = l_Lean_Name_str___override(v___x_4667_, v___x_4666_);
return v___x_4668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4672_ = l_Lean_Name_str___override(v___x_4671_, v___x_4670_);
return v___x_4672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4673_ = lean_unsigned_to_nat(2u);
v___x_4674_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4675_ = l_Lean_Name_num___override(v___x_4674_, v___x_4673_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4677_; uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4678_ = 0;
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4680_ = l_Lean_registerTraceClass(v___x_4677_, v___x_4678_, v___x_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4682_;
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
