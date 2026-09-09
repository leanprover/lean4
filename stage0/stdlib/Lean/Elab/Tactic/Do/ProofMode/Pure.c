// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Pure
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal import Lean.Elab.Tactic.Meta import Lean.Elab.Tactic.Do.ProofMode.Basic import Lean.Elab.Tactic.Do.ProofMode.Focus import Lean.Meta.Tactic.Rfl
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "IsPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_mkFreshLevelMVar___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mpure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 40, 78, 170, 57, 132, 109, 163)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMPure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 32, 90, 224, 99, 186, 132, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 186, 166, 18, 114, 151, 126, 123)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 69, 55, 193, 136, 208, 207, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mpureIntro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 145, 131, 67, 32, 11, 101, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabMPureIntro"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 186, 47, 90, 191, 89, 235, 189)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ULift"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "down"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 162, 24, 1, 186, 170, 9, 57)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(8, 0, 133, 161, 22, 18, 91, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 183, 133, 62, 214, 202, 136, 98)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_applyRflAndAndIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__0 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__1 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__1_value;
static const lean_string_object l_Lean_MVarId_applyRflAndAndIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__2 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__3 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__4 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__4_value;
static lean_once_cell_t l_Lean_MVarId_applyRflAndAndIntro___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__5;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__6 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_applyRflAndAndIntro___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__7;
static const lean_string_object l_Lean_MVarId_applyRflAndAndIntro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__8 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__8_value;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_2),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 14, 123, 28, 194, 252, 167, 244)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__9 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value;
static const lean_string_object l_Lean_MVarId_applyRflAndAndIntro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__10 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__10_value;
static const lean_ctor_object l_Lean_MVarId_applyRflAndAndIntro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__11 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__11_value;
static lean_once_cell_t l_Lean_MVarId_applyRflAndAndIntro___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__12;
static const lean_string_object l_Lean_MVarId_applyRflAndAndIntro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pure Prop: "};
static const lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__13 = (const lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__13_value;
static lean_once_cell_t l_Lean_MVarId_applyRflAndAndIntro___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_applyRflAndAndIntro___closed__14;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRflAndAndIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRflAndAndIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "discharged: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "discharge\? "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value),((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "pureRflAndAndIntro: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticTrivial"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 113, 211, 1, 53, 106, 100, 38)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(lean_object* v___y_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v_lctx_6_; lean_object* v___x_7_; 
v_lctx_6_ = lean_ctor_get(v___y_1_, 2);
lean_inc_ref(v_lctx_6_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_lctx_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed(lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(v___y_8_, v___y_9_, v___y_10_, v___y_11_);
lean_dec(v___y_11_);
lean_dec_ref(v___y_10_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(lean_object* v_name_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_14_, v___y_17_, v___y_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed(lean_object* v_name_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(v_name_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2(lean_object* v_fst_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v_00_u03c3s_36_, lean_object* v_hyp_37_, lean_object* v_00_u03c6_38_, lean_object* v_inst_39_, lean_object* v_u_40_, lean_object* v_fst_41_, lean_object* v_toPure_42_, lean_object* v_prf_43_){
_start:
{
lean_object* v_u_44_; lean_object* v_00_u03c3s_45_; lean_object* v_hyps_46_; lean_object* v_target_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_63_; 
v_u_44_ = lean_ctor_get(v_fst_30_, 0);
v_00_u03c3s_45_ = lean_ctor_get(v_fst_30_, 1);
v_hyps_46_ = lean_ctor_get(v_fst_30_, 2);
v_target_47_ = lean_ctor_get(v_fst_30_, 3);
v_isSharedCheck_63_ = !lean_is_exclusive(v_fst_30_);
if (v_isSharedCheck_63_ == 0)
{
v___x_49_ = v_fst_30_;
v_isShared_50_ = v_isSharedCheck_63_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_target_47_);
lean_inc(v_hyps_46_);
lean_inc(v_00_u03c3s_45_);
lean_inc(v_u_44_);
lean_dec(v_fst_30_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_63_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_prf_55_; lean_object* v___x_56_; lean_object* v_goal_58_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_52_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1));
v___x_53_ = l_Lean_Name_mkStr6(v___x_31_, v___x_32_, v___x_33_, v___x_34_, v___x_51_, v___x_52_);
v___x_54_ = l_Lean_mkConst(v___x_53_, v___x_35_);
lean_inc_ref(v_target_47_);
lean_inc_ref(v_hyp_37_);
lean_inc_ref(v_hyps_46_);
lean_inc_ref(v_00_u03c3s_36_);
v_prf_55_ = l_Lean_mkApp7(v___x_54_, v_00_u03c3s_36_, v_hyps_46_, v_hyp_37_, v_target_47_, v_00_u03c6_38_, v_inst_39_, v_prf_43_);
v___x_56_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_40_, v_00_u03c3s_36_, v_hyps_46_, v_hyp_37_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_56_);
v_goal_58_ = v___x_49_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_u_44_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_00_u03c3s_45_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_target_47_);
v_goal_58_ = v_reuseFailAlloc_62_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_goal_58_);
lean_ctor_set(v___x_59_, 1, v_prf_55_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_fst_41_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_60_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(lean_object* v___x_64_, lean_object* v___x_65_, lean_object* v___x_66_, lean_object* v___x_67_, lean_object* v___x_68_, lean_object* v_00_u03c3s_69_, lean_object* v_hyp_70_, lean_object* v_00_u03c6_71_, lean_object* v_inst_72_, lean_object* v_u_73_, lean_object* v_toPure_74_, lean_object* v_h_75_, uint8_t v___x_76_, lean_object* v_inst_77_, lean_object* v_toBind_78_, lean_object* v_____x_79_){
_start:
{
lean_object* v_snd_80_; lean_object* v_fst_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_snd_80_ = lean_ctor_get(v_____x_79_, 1);
lean_inc(v_snd_80_);
v_fst_81_ = lean_ctor_get(v_____x_79_, 0);
lean_inc(v_fst_81_);
lean_dec_ref(v_____x_79_);
v_fst_82_ = lean_ctor_get(v_snd_80_, 0);
lean_inc(v_fst_82_);
v_snd_83_ = lean_ctor_get(v_snd_80_, 1);
lean_inc(v_snd_83_);
lean_dec(v_snd_80_);
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2), 14, 13);
lean_closure_set(v___f_84_, 0, v_fst_82_);
lean_closure_set(v___f_84_, 1, v___x_64_);
lean_closure_set(v___f_84_, 2, v___x_65_);
lean_closure_set(v___f_84_, 3, v___x_66_);
lean_closure_set(v___f_84_, 4, v___x_67_);
lean_closure_set(v___f_84_, 5, v___x_68_);
lean_closure_set(v___f_84_, 6, v_00_u03c3s_69_);
lean_closure_set(v___f_84_, 7, v_hyp_70_);
lean_closure_set(v___f_84_, 8, v_00_u03c6_71_);
lean_closure_set(v___f_84_, 9, v_inst_72_);
lean_closure_set(v___f_84_, 10, v_u_73_);
lean_closure_set(v___f_84_, 11, v_fst_81_);
lean_closure_set(v___f_84_, 12, v_toPure_74_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_mk_empty_array_with_capacity(v___x_85_);
v___x_87_ = lean_array_push(v___x_86_, v_h_75_);
v___x_88_ = 1;
v___x_89_ = 1;
v___x_90_ = lean_box(v___x_76_);
v___x_91_ = lean_box(v___x_88_);
v___x_92_ = lean_box(v___x_76_);
v___x_93_ = lean_box(v___x_88_);
v___x_94_ = lean_box(v___x_89_);
v___x_95_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_95_, 0, v___x_87_);
lean_closure_set(v___x_95_, 1, v_snd_83_);
lean_closure_set(v___x_95_, 2, v___x_90_);
lean_closure_set(v___x_95_, 3, v___x_91_);
lean_closure_set(v___x_95_, 4, v___x_92_);
lean_closure_set(v___x_95_, 5, v___x_93_);
lean_closure_set(v___x_95_, 6, v___x_94_);
v___x_96_ = lean_apply_2(v_inst_77_, lean_box(0), v___x_95_);
v___x_97_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_96_, v___f_84_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed(lean_object* v___x_98_, lean_object* v___x_99_, lean_object* v___x_100_, lean_object* v___x_101_, lean_object* v___x_102_, lean_object* v_00_u03c3s_103_, lean_object* v_hyp_104_, lean_object* v_00_u03c6_105_, lean_object* v_inst_106_, lean_object* v_u_107_, lean_object* v_toPure_108_, lean_object* v_h_109_, lean_object* v___x_110_, lean_object* v_inst_111_, lean_object* v_toBind_112_, lean_object* v_____x_113_){
_start:
{
uint8_t v___x_486__boxed_114_; lean_object* v_res_115_; 
v___x_486__boxed_114_ = lean_unbox(v___x_110_);
v_res_115_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(v___x_98_, v___x_99_, v___x_100_, v___x_101_, v___x_102_, v_00_u03c3s_103_, v_hyp_104_, v_00_u03c6_105_, v_inst_106_, v_u_107_, v_toPure_108_, v_h_109_, v___x_486__boxed_114_, v_inst_111_, v_toBind_112_, v_____x_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4(lean_object* v_k_116_, lean_object* v_00_u03c6_117_, lean_object* v_h_118_, lean_object* v_toBind_119_, lean_object* v___f_120_, lean_object* v_____r_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_apply_2(v_k_116_, v_00_u03c6_117_, v_h_118_);
v___x_123_ = lean_apply_4(v_toBind_119_, lean_box(0), lean_box(0), v___x_122_, v___f_120_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(lean_object* v_00_u03c6_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v___x_127_, lean_object* v___x_128_, lean_object* v___x_129_, lean_object* v_00_u03c3s_130_, lean_object* v_hyp_131_, lean_object* v_inst_132_, lean_object* v_u_133_, lean_object* v_toPure_134_, lean_object* v_h_135_, lean_object* v_inst_136_, lean_object* v_toBind_137_, lean_object* v_k_138_, lean_object* v_snd_139_, lean_object* v_____do__lift_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc_ref_n(v_00_u03c6_124_, 2);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_00_u03c6_124_);
v___x_142_ = 0;
v___x_143_ = lean_box(v___x_142_);
lean_inc_n(v_toBind_137_, 2);
lean_inc(v_inst_136_);
lean_inc_ref_n(v_h_135_, 2);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_144_, 0, v___x_125_);
lean_closure_set(v___f_144_, 1, v___x_126_);
lean_closure_set(v___f_144_, 2, v___x_127_);
lean_closure_set(v___f_144_, 3, v___x_128_);
lean_closure_set(v___f_144_, 4, v___x_129_);
lean_closure_set(v___f_144_, 5, v_00_u03c3s_130_);
lean_closure_set(v___f_144_, 6, v_hyp_131_);
lean_closure_set(v___f_144_, 7, v_00_u03c6_124_);
lean_closure_set(v___f_144_, 8, v_inst_132_);
lean_closure_set(v___f_144_, 9, v_u_133_);
lean_closure_set(v___f_144_, 10, v_toPure_134_);
lean_closure_set(v___f_144_, 11, v_h_135_);
lean_closure_set(v___f_144_, 12, v___x_143_);
lean_closure_set(v___f_144_, 13, v_inst_136_);
lean_closure_set(v___f_144_, 14, v_toBind_137_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4), 6, 5);
lean_closure_set(v___f_145_, 0, v_k_138_);
lean_closure_set(v___f_145_, 1, v_00_u03c6_124_);
lean_closure_set(v___f_145_, 2, v_h_135_);
lean_closure_set(v___f_145_, 3, v_toBind_137_);
lean_closure_set(v___f_145_, 4, v___f_144_);
v___x_146_ = lean_box(v___x_142_);
v___x_147_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed), 10, 5);
lean_closure_set(v___x_147_, 0, v_snd_139_);
lean_closure_set(v___x_147_, 1, v_____do__lift_140_);
lean_closure_set(v___x_147_, 2, v_h_135_);
lean_closure_set(v___x_147_, 3, v___x_141_);
lean_closure_set(v___x_147_, 4, v___x_146_);
v___x_148_ = lean_apply_2(v_inst_136_, lean_box(0), v___x_147_);
v___x_149_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_148_, v___f_145_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_00_u03c6_150_ = _args[0];
lean_object* v___x_151_ = _args[1];
lean_object* v___x_152_ = _args[2];
lean_object* v___x_153_ = _args[3];
lean_object* v___x_154_ = _args[4];
lean_object* v___x_155_ = _args[5];
lean_object* v_00_u03c3s_156_ = _args[6];
lean_object* v_hyp_157_ = _args[7];
lean_object* v_inst_158_ = _args[8];
lean_object* v_u_159_ = _args[9];
lean_object* v_toPure_160_ = _args[10];
lean_object* v_h_161_ = _args[11];
lean_object* v_inst_162_ = _args[12];
lean_object* v_toBind_163_ = _args[13];
lean_object* v_k_164_ = _args[14];
lean_object* v_snd_165_ = _args[15];
lean_object* v_____do__lift_166_ = _args[16];
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(v_00_u03c6_150_, v___x_151_, v___x_152_, v___x_153_, v___x_154_, v___x_155_, v_00_u03c3s_156_, v_hyp_157_, v_inst_158_, v_u_159_, v_toPure_160_, v_h_161_, v_inst_162_, v_toBind_163_, v_k_164_, v_snd_165_, v_____do__lift_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(lean_object* v_00_u03c6_168_, lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v___x_171_, lean_object* v___x_172_, lean_object* v___x_173_, lean_object* v_00_u03c3s_174_, lean_object* v_hyp_175_, lean_object* v_inst_176_, lean_object* v_u_177_, lean_object* v_toPure_178_, lean_object* v_inst_179_, lean_object* v_toBind_180_, lean_object* v_k_181_, lean_object* v_snd_182_, lean_object* v___f_183_, lean_object* v_h_184_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_inc(v_toBind_180_);
lean_inc(v_inst_179_);
v___f_185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_185_, 0, v_00_u03c6_168_);
lean_closure_set(v___f_185_, 1, v___x_169_);
lean_closure_set(v___f_185_, 2, v___x_170_);
lean_closure_set(v___f_185_, 3, v___x_171_);
lean_closure_set(v___f_185_, 4, v___x_172_);
lean_closure_set(v___f_185_, 5, v___x_173_);
lean_closure_set(v___f_185_, 6, v_00_u03c3s_174_);
lean_closure_set(v___f_185_, 7, v_hyp_175_);
lean_closure_set(v___f_185_, 8, v_inst_176_);
lean_closure_set(v___f_185_, 9, v_u_177_);
lean_closure_set(v___f_185_, 10, v_toPure_178_);
lean_closure_set(v___f_185_, 11, v_h_184_);
lean_closure_set(v___f_185_, 12, v_inst_179_);
lean_closure_set(v___f_185_, 13, v_toBind_180_);
lean_closure_set(v___f_185_, 14, v_k_181_);
lean_closure_set(v___f_185_, 15, v_snd_182_);
v___x_186_ = lean_apply_2(v_inst_179_, lean_box(0), v___f_183_);
v___x_187_ = lean_apply_4(v_toBind_180_, lean_box(0), lean_box(0), v___x_186_, v___f_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_00_u03c6_188_ = _args[0];
lean_object* v___x_189_ = _args[1];
lean_object* v___x_190_ = _args[2];
lean_object* v___x_191_ = _args[3];
lean_object* v___x_192_ = _args[4];
lean_object* v___x_193_ = _args[5];
lean_object* v_00_u03c3s_194_ = _args[6];
lean_object* v_hyp_195_ = _args[7];
lean_object* v_inst_196_ = _args[8];
lean_object* v_u_197_ = _args[9];
lean_object* v_toPure_198_ = _args[10];
lean_object* v_inst_199_ = _args[11];
lean_object* v_toBind_200_ = _args[12];
lean_object* v_k_201_ = _args[13];
lean_object* v_snd_202_ = _args[14];
lean_object* v___f_203_ = _args[15];
lean_object* v_h_204_ = _args[16];
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(v_00_u03c6_188_, v___x_189_, v___x_190_, v___x_191_, v___x_192_, v___x_193_, v_00_u03c3s_194_, v_hyp_195_, v_inst_196_, v_u_197_, v_toPure_198_, v_inst_199_, v_toBind_200_, v_k_201_, v_snd_202_, v___f_203_, v_h_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(lean_object* v_00_u03c6_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v___x_209_, lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v_00_u03c3s_212_, lean_object* v_hyp_213_, lean_object* v_inst_214_, lean_object* v_u_215_, lean_object* v_toPure_216_, lean_object* v_inst_217_, lean_object* v_toBind_218_, lean_object* v_k_219_, lean_object* v___f_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_____x_223_){
_start:
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___f_226_; lean_object* v___x_227_; 
v_fst_224_ = lean_ctor_get(v_____x_223_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_____x_223_, 1);
lean_inc(v_snd_225_);
lean_dec_ref(v_____x_223_);
lean_inc_ref(v_00_u03c6_206_);
v___f_226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_226_, 0, v_00_u03c6_206_);
lean_closure_set(v___f_226_, 1, v___x_207_);
lean_closure_set(v___f_226_, 2, v___x_208_);
lean_closure_set(v___f_226_, 3, v___x_209_);
lean_closure_set(v___f_226_, 4, v___x_210_);
lean_closure_set(v___f_226_, 5, v___x_211_);
lean_closure_set(v___f_226_, 6, v_00_u03c3s_212_);
lean_closure_set(v___f_226_, 7, v_hyp_213_);
lean_closure_set(v___f_226_, 8, v_inst_214_);
lean_closure_set(v___f_226_, 9, v_u_215_);
lean_closure_set(v___f_226_, 10, v_toPure_216_);
lean_closure_set(v___f_226_, 11, v_inst_217_);
lean_closure_set(v___f_226_, 12, v_toBind_218_);
lean_closure_set(v___f_226_, 13, v_k_219_);
lean_closure_set(v___f_226_, 14, v_snd_225_);
lean_closure_set(v___f_226_, 15, v___f_220_);
v___x_227_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_221_, v_inst_222_, v_fst_224_, v_00_u03c6_206_, v___f_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_00_u03c6_228_ = _args[0];
lean_object* v___x_229_ = _args[1];
lean_object* v___x_230_ = _args[2];
lean_object* v___x_231_ = _args[3];
lean_object* v___x_232_ = _args[4];
lean_object* v___x_233_ = _args[5];
lean_object* v_00_u03c3s_234_ = _args[6];
lean_object* v_hyp_235_ = _args[7];
lean_object* v_inst_236_ = _args[8];
lean_object* v_u_237_ = _args[9];
lean_object* v_toPure_238_ = _args[10];
lean_object* v_inst_239_ = _args[11];
lean_object* v_toBind_240_ = _args[12];
lean_object* v_k_241_ = _args[13];
lean_object* v___f_242_ = _args[14];
lean_object* v_inst_243_ = _args[15];
lean_object* v_inst_244_ = _args[16];
lean_object* v_____x_245_ = _args[17];
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(v_00_u03c6_228_, v___x_229_, v___x_230_, v___x_231_, v___x_232_, v___x_233_, v_00_u03c3s_234_, v_hyp_235_, v_inst_236_, v_u_237_, v_toPure_238_, v_inst_239_, v_toBind_240_, v_k_241_, v___f_242_, v_inst_243_, v_inst_244_, v_____x_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(lean_object* v_00_u03c6_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v___x_252_, lean_object* v_00_u03c3s_253_, lean_object* v_hyp_254_, lean_object* v_u_255_, lean_object* v_toPure_256_, lean_object* v_inst_257_, lean_object* v_toBind_258_, lean_object* v_k_259_, lean_object* v___f_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v___f_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc(v_toBind_258_);
lean_inc(v_inst_257_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_265_, 0, v_00_u03c6_247_);
lean_closure_set(v___f_265_, 1, v___x_248_);
lean_closure_set(v___f_265_, 2, v___x_249_);
lean_closure_set(v___f_265_, 3, v___x_250_);
lean_closure_set(v___f_265_, 4, v___x_251_);
lean_closure_set(v___f_265_, 5, v___x_252_);
lean_closure_set(v___f_265_, 6, v_00_u03c3s_253_);
lean_closure_set(v___f_265_, 7, v_hyp_254_);
lean_closure_set(v___f_265_, 8, v_inst_264_);
lean_closure_set(v___f_265_, 9, v_u_255_);
lean_closure_set(v___f_265_, 10, v_toPure_256_);
lean_closure_set(v___f_265_, 11, v_inst_257_);
lean_closure_set(v___f_265_, 12, v_toBind_258_);
lean_closure_set(v___f_265_, 13, v_k_259_);
lean_closure_set(v___f_265_, 14, v___f_260_);
lean_closure_set(v___f_265_, 15, v_inst_261_);
lean_closure_set(v___f_265_, 16, v_inst_262_);
v___x_266_ = lean_apply_2(v_inst_257_, lean_box(0), v___f_263_);
v___x_267_ = lean_apply_4(v_toBind_258_, lean_box(0), lean_box(0), v___x_266_, v___f_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_00_u03c6_268_ = _args[0];
lean_object* v___x_269_ = _args[1];
lean_object* v___x_270_ = _args[2];
lean_object* v___x_271_ = _args[3];
lean_object* v___x_272_ = _args[4];
lean_object* v___x_273_ = _args[5];
lean_object* v_00_u03c3s_274_ = _args[6];
lean_object* v_hyp_275_ = _args[7];
lean_object* v_u_276_ = _args[8];
lean_object* v_toPure_277_ = _args[9];
lean_object* v_inst_278_ = _args[10];
lean_object* v_toBind_279_ = _args[11];
lean_object* v_k_280_ = _args[12];
lean_object* v___f_281_ = _args[13];
lean_object* v_inst_282_ = _args[14];
lean_object* v_inst_283_ = _args[15];
lean_object* v___f_284_ = _args[16];
lean_object* v_inst_285_ = _args[17];
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(v_00_u03c6_268_, v___x_269_, v___x_270_, v___x_271_, v___x_272_, v___x_273_, v_00_u03c3s_274_, v_hyp_275_, v_u_276_, v_toPure_277_, v_inst_278_, v_toBind_279_, v_k_280_, v___f_281_, v_inst_282_, v_inst_283_, v___f_284_, v_inst_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9(lean_object* v_u_298_, lean_object* v_00_u03c3s_299_, lean_object* v_hyp_300_, lean_object* v_toPure_301_, lean_object* v_inst_302_, lean_object* v_toBind_303_, lean_object* v_k_304_, lean_object* v___f_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v___f_308_, lean_object* v_00_u03c6_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_311_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_312_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_314_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_315_ = lean_box(0);
lean_inc(v_u_298_);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v_u_298_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
lean_inc(v_toBind_303_);
lean_inc(v_inst_302_);
lean_inc_ref(v_hyp_300_);
lean_inc_ref(v_00_u03c3s_299_);
lean_inc_ref(v___x_316_);
lean_inc_ref(v_00_u03c6_309_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed), 18, 17);
lean_closure_set(v___f_317_, 0, v_00_u03c6_309_);
lean_closure_set(v___f_317_, 1, v___x_310_);
lean_closure_set(v___f_317_, 2, v___x_311_);
lean_closure_set(v___f_317_, 3, v___x_312_);
lean_closure_set(v___f_317_, 4, v___x_313_);
lean_closure_set(v___f_317_, 5, v___x_316_);
lean_closure_set(v___f_317_, 6, v_00_u03c3s_299_);
lean_closure_set(v___f_317_, 7, v_hyp_300_);
lean_closure_set(v___f_317_, 8, v_u_298_);
lean_closure_set(v___f_317_, 9, v_toPure_301_);
lean_closure_set(v___f_317_, 10, v_inst_302_);
lean_closure_set(v___f_317_, 11, v_toBind_303_);
lean_closure_set(v___f_317_, 12, v_k_304_);
lean_closure_set(v___f_317_, 13, v___f_305_);
lean_closure_set(v___f_317_, 14, v_inst_306_);
lean_closure_set(v___f_317_, 15, v_inst_307_);
lean_closure_set(v___f_317_, 16, v___f_308_);
v___x_318_ = l_Lean_mkConst(v___x_314_, v___x_316_);
v___x_319_ = l_Lean_mkApp3(v___x_318_, v_00_u03c3s_299_, v_hyp_300_, v_00_u03c6_309_);
v___x_320_ = lean_box(0);
v___x_321_ = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance___boxed), 7, 2);
lean_closure_set(v___x_321_, 0, v___x_319_);
lean_closure_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_apply_2(v_inst_302_, lean_box(0), v___x_321_);
v___x_323_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v___x_322_, v___f_317_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_mkSort(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2(void){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = lean_box(0);
v___x_329_ = 0;
v___x_330_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_331_ = lean_box(v___x_329_);
v___x_332_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_332_, 0, v___x_330_);
lean_closure_set(v___x_332_, 1, v___x_331_);
lean_closure_set(v___x_332_, 2, v___x_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10(lean_object* v_00_u03c3s_333_, lean_object* v_hyp_334_, lean_object* v_toPure_335_, lean_object* v_inst_336_, lean_object* v_toBind_337_, lean_object* v_k_338_, lean_object* v___f_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v___f_342_, lean_object* v_u_343_){
_start:
{
lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc(v_toBind_337_);
lean_inc(v_inst_336_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9), 12, 11);
lean_closure_set(v___f_344_, 0, v_u_343_);
lean_closure_set(v___f_344_, 1, v_00_u03c3s_333_);
lean_closure_set(v___f_344_, 2, v_hyp_334_);
lean_closure_set(v___f_344_, 3, v_toPure_335_);
lean_closure_set(v___f_344_, 4, v_inst_336_);
lean_closure_set(v___f_344_, 5, v_toBind_337_);
lean_closure_set(v___f_344_, 6, v_k_338_);
lean_closure_set(v___f_344_, 7, v___f_339_);
lean_closure_set(v___f_344_, 8, v_inst_340_);
lean_closure_set(v___f_344_, 9, v_inst_341_);
lean_closure_set(v___f_344_, 10, v___f_342_);
v___x_345_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2);
v___x_346_ = lean_apply_2(v_inst_336_, lean_box(0), v___x_345_);
v___x_347_ = lean_apply_4(v_toBind_337_, lean_box(0), lean_box(0), v___x_346_, v___f_344_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_00_u03c3s_353_, lean_object* v_hyp_354_, lean_object* v_name_355_, lean_object* v_k_356_){
_start:
{
lean_object* v_toApplicative_357_; lean_object* v_toBind_358_; lean_object* v_toPure_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_toApplicative_357_ = lean_ctor_get(v_inst_350_, 0);
v_toBind_358_ = lean_ctor_get(v_inst_350_, 1);
lean_inc_n(v_toBind_358_, 2);
v_toPure_359_ = lean_ctor_get(v_toApplicative_357_, 1);
lean_inc(v_toPure_359_);
v___f_360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0));
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_361_, 0, v_name_355_);
v___x_362_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1));
lean_inc(v_inst_352_);
v___x_363_ = lean_apply_2(v_inst_352_, lean_box(0), v___x_362_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10), 11, 10);
lean_closure_set(v___f_364_, 0, v_00_u03c3s_353_);
lean_closure_set(v___f_364_, 1, v_hyp_354_);
lean_closure_set(v___f_364_, 2, v_toPure_359_);
lean_closure_set(v___f_364_, 3, v_inst_352_);
lean_closure_set(v___f_364_, 4, v_toBind_358_);
lean_closure_set(v___f_364_, 5, v_k_356_);
lean_closure_set(v___f_364_, 6, v___f_360_);
lean_closure_set(v___f_364_, 7, v_inst_351_);
lean_closure_set(v___f_364_, 8, v_inst_350_);
lean_closure_set(v___f_364_, 9, v___f_361_);
v___x_365_ = lean_apply_4(v_toBind_358_, lean_box(0), lean_box(0), v___x_363_, v___f_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore(lean_object* v_m_366_, lean_object* v_00_u03b1_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_00_u03c3s_371_, lean_object* v_hyp_372_, lean_object* v_name_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(v_inst_368_, v_inst_369_, v_inst_370_, v_00_u03c3s_371_, v_hyp_372_, v_name_373_, v_k_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg(){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___boxed(lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(lean_object* v_00_u03b1_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___boxed(lean_object* v_00_u03b1_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(v_00_u03b1_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(lean_object* v_x_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_416_; 
lean_inc(v___y_410_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc_ref(v___y_407_);
v___x_416_ = lean_apply_9(v_x_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, lean_box(0));
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed(lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(v_x_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(lean_object* v_mvarId_428_, lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; 
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___f_439_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_439_, 0, v_x_429_);
lean_closure_set(v___f_439_, 1, v___y_430_);
lean_closure_set(v___f_439_, 2, v___y_431_);
lean_closure_set(v___f_439_, 3, v___y_432_);
lean_closure_set(v___f_439_, 4, v___y_433_);
v___x_440_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_428_, v___f_439_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
return v___x_440_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___boxed(lean_object* v_mvarId_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_mvarId_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(lean_object* v_00_u03b1_461_, lean_object* v_mvarId_462_, lean_object* v_x_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_mvarId_462_, v_x_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___boxed(lean_object* v_00_u03b1_474_, lean_object* v_mvarId_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(v_00_u03b1_474_, v_mvarId_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(lean_object* v_a_487_, lean_object* v_snd_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_a_487_, v_snd_488_);
lean_inc_ref(v___x_500_);
v___x_501_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_500_);
v___x_502_ = lean_box(0);
v___x_503_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_501_, v___x_502_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_513_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_513_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
lean_inc(v_a_504_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_500_);
lean_ctor_set(v___x_508_, 1, v_a_504_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_a_504_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v___x_500_);
v_a_514_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_503_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_503_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed(lean_object* v_a_522_, lean_object* v_snd_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(v_a_522_, v_snd_523_, v_x_524_, v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v_x_525_);
lean_dec_ref(v_x_524_);
lean_dec_ref(v_a_522_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_k_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
lean_inc(v___y_545_);
lean_inc_ref(v___y_544_);
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_547_ = lean_apply_10(v_k_536_, v_b_541_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, lean_box(0));
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v_k_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(v_k_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(lean_object* v_name_560_, uint8_t v_bi_561_, lean_object* v_type_562_, lean_object* v_k_563_, uint8_t v_kind_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___f_574_; lean_object* v___x_575_; 
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_574_, 0, v_k_563_);
lean_closure_set(v___f_574_, 1, v___y_565_);
lean_closure_set(v___f_574_, 2, v___y_566_);
lean_closure_set(v___f_574_, 3, v___y_567_);
lean_closure_set(v___f_574_, 4, v___y_568_);
v___x_575_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_560_, v_bi_561_, v_type_562_, v___f_574_, v_kind_564_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_575_) == 0)
{
return v___x_575_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_name_584_, lean_object* v_bi_585_, lean_object* v_type_586_, lean_object* v_k_587_, lean_object* v_kind_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_bi_boxed_598_; uint8_t v_kind_boxed_599_; lean_object* v_res_600_; 
v_bi_boxed_598_ = lean_unbox(v_bi_585_);
v_kind_boxed_599_ = lean_unbox(v_kind_588_);
v_res_600_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_584_, v_bi_boxed_598_, v_type_586_, v_k_587_, v_kind_boxed_599_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(lean_object* v_name_601_, lean_object* v_type_602_, lean_object* v_k_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = 0;
v___x_614_ = 0;
v___x_615_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_601_, v___x_613_, v_type_602_, v_k_603_, v___x_614_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg___boxed(lean_object* v_name_616_, lean_object* v_type_617_, lean_object* v_k_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_616_, v_type_617_, v_k_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(lean_object* v_a_629_, lean_object* v_snd_630_, lean_object* v_k_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v_00_u03c3s_637_, lean_object* v_hyp_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_h_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_lctx_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; 
v_lctx_651_ = lean_ctor_get(v___y_646_, 2);
lean_inc_ref(v_a_629_);
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v_a_629_);
v___x_653_ = 0;
lean_inc_ref(v_h_641_);
lean_inc_ref(v_lctx_651_);
v___x_654_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_630_, v_lctx_651_, v_h_641_, v___x_652_, v___x_653_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
lean_dec_ref_known(v___x_654_, 1);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc_ref(v_h_641_);
lean_inc_ref(v_a_629_);
v___x_655_ = lean_apply_11(v_k_631_, v_a_629_, v_h_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_snd_657_; lean_object* v_fst_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_713_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v_snd_657_ = lean_ctor_get(v_a_656_, 1);
v_fst_658_ = lean_ctor_get(v_a_656_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_713_ == 0)
{
v___x_660_ = v_a_656_;
v_isShared_661_ = v_isSharedCheck_713_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_658_);
lean_dec(v_a_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_713_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_712_; 
v_fst_662_ = lean_ctor_get(v_snd_657_, 0);
v_snd_663_ = lean_ctor_get(v_snd_657_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_snd_657_);
if (v_isSharedCheck_712_ == 0)
{
v___x_665_ = v_snd_657_;
v_isShared_666_ = v_isSharedCheck_712_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_snd_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_712_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_array_push(v___x_668_, v_h_641_);
v___x_670_ = 1;
v___x_671_ = 1;
v___x_672_ = l_Lean_Meta_mkLambdaFVars(v___x_669_, v_snd_663_, v___x_653_, v___x_670_, v___x_653_, v___x_670_, v___x_671_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec_ref(v___x_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_703_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_703_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_u_677_; lean_object* v_00_u03c3s_678_; lean_object* v_hyps_679_; lean_object* v_target_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_702_; 
v_u_677_ = lean_ctor_get(v_fst_662_, 0);
v_00_u03c3s_678_ = lean_ctor_get(v_fst_662_, 1);
v_hyps_679_ = lean_ctor_get(v_fst_662_, 2);
v_target_680_ = lean_ctor_get(v_fst_662_, 3);
v_isSharedCheck_702_ = !lean_is_exclusive(v_fst_662_);
if (v_isSharedCheck_702_ == 0)
{
v___x_682_ = v_fst_662_;
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_target_680_);
lean_inc(v_hyps_679_);
lean_inc(v_00_u03c3s_678_);
lean_inc(v_u_677_);
lean_dec(v_fst_662_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_prf_688_; lean_object* v___x_689_; lean_object* v_goal_691_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1));
v___x_686_ = l_Lean_Name_mkStr6(v___x_632_, v___x_633_, v___x_634_, v___x_635_, v___x_684_, v___x_685_);
v___x_687_ = l_Lean_mkConst(v___x_686_, v___x_636_);
lean_inc_ref(v_target_680_);
lean_inc_ref(v_hyp_638_);
lean_inc_ref(v_hyps_679_);
lean_inc_ref(v_00_u03c3s_637_);
v_prf_688_ = l_Lean_mkApp7(v___x_687_, v_00_u03c3s_637_, v_hyps_679_, v_hyp_638_, v_target_680_, v_a_629_, v_a_639_, v_a_673_);
v___x_689_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_640_, v_00_u03c3s_637_, v_hyps_679_, v_hyp_638_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 2, v___x_689_);
v_goal_691_ = v___x_682_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_u_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_00_u03c3s_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_target_680_);
v_goal_691_ = v_reuseFailAlloc_701_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_prf_688_);
lean_ctor_set(v___x_665_, 0, v_goal_691_);
v___x_693_ = v___x_665_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_goal_691_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_prf_688_);
v___x_693_ = v_reuseFailAlloc_700_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_693_);
v___x_695_ = v___x_660_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_fst_658_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_695_);
v___x_697_ = v___x_675_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_del_object(v___x_665_);
lean_dec(v_fst_662_);
lean_del_object(v___x_660_);
lean_dec(v_fst_658_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec_ref(v_hyp_638_);
lean_dec_ref(v_00_u03c3s_637_);
lean_dec(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v_a_629_);
v_a_704_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_672_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_672_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec_ref(v_hyp_638_);
lean_dec_ref(v_00_u03c3s_637_);
lean_dec(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v_a_629_);
return v___x_655_;
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_h_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec_ref(v_hyp_638_);
lean_dec_ref(v_00_u03c3s_637_);
lean_dec(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v_k_631_);
lean_dec_ref(v_a_629_);
v_a_714_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_654_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_654_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_722_ = _args[0];
lean_object* v_snd_723_ = _args[1];
lean_object* v_k_724_ = _args[2];
lean_object* v___x_725_ = _args[3];
lean_object* v___x_726_ = _args[4];
lean_object* v___x_727_ = _args[5];
lean_object* v___x_728_ = _args[6];
lean_object* v___x_729_ = _args[7];
lean_object* v_00_u03c3s_730_ = _args[8];
lean_object* v_hyp_731_ = _args[9];
lean_object* v_a_732_ = _args[10];
lean_object* v_a_733_ = _args[11];
lean_object* v_h_734_ = _args[12];
lean_object* v___y_735_ = _args[13];
lean_object* v___y_736_ = _args[14];
lean_object* v___y_737_ = _args[15];
lean_object* v___y_738_ = _args[16];
lean_object* v___y_739_ = _args[17];
lean_object* v___y_740_ = _args[18];
lean_object* v___y_741_ = _args[19];
lean_object* v___y_742_ = _args[20];
lean_object* v___y_743_ = _args[21];
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(v_a_722_, v_snd_723_, v_k_724_, v___x_725_, v___x_726_, v___x_727_, v___x_728_, v___x_729_, v_00_u03c3s_730_, v_hyp_731_, v_a_732_, v_a_733_, v_h_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(lean_object* v_00_u03c3s_745_, lean_object* v_hyp_746_, lean_object* v_name_747_, lean_object* v_k_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_mkFreshLevelMVar(v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_761_ = 0;
v___x_762_ = lean_box(0);
v___x_763_ = l_Lean_Meta_mkFreshExprMVar(v___x_760_, v___x_761_, v___x_762_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_n(v_a_764_, 2);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_770_ = lean_box(0);
lean_inc(v_a_759_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v_a_759_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_inc_ref(v___x_771_);
v___x_772_ = l_Lean_mkConst(v___x_769_, v___x_771_);
lean_inc_ref(v_hyp_746_);
lean_inc_ref(v_00_u03c3s_745_);
v___x_773_ = l_Lean_mkApp3(v___x_772_, v_00_u03c3s_745_, v_hyp_746_, v_a_764_);
v___x_774_ = lean_box(0);
v___x_775_ = l_Lean_Meta_synthInstance(v___x_773_, v___x_774_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_747_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___f_781_; lean_object* v___x_782_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v_fst_779_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_fst_779_);
v_snd_780_ = lean_ctor_get(v_a_778_, 1);
lean_inc(v_snd_780_);
lean_dec(v_a_778_);
lean_inc(v_a_764_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed), 22, 12);
lean_closure_set(v___f_781_, 0, v_a_764_);
lean_closure_set(v___f_781_, 1, v_snd_780_);
lean_closure_set(v___f_781_, 2, v_k_748_);
lean_closure_set(v___f_781_, 3, v___x_765_);
lean_closure_set(v___f_781_, 4, v___x_766_);
lean_closure_set(v___f_781_, 5, v___x_767_);
lean_closure_set(v___f_781_, 6, v___x_768_);
lean_closure_set(v___f_781_, 7, v___x_771_);
lean_closure_set(v___f_781_, 8, v_00_u03c3s_745_);
lean_closure_set(v___f_781_, 9, v_hyp_746_);
lean_closure_set(v___f_781_, 10, v_a_776_);
lean_closure_set(v___f_781_, 11, v_a_759_);
v___x_782_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_fst_779_, v_a_764_, v___f_781_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_776_);
lean_dec_ref_known(v___x_771_, 2);
lean_dec(v_a_764_);
lean_dec(v_a_759_);
lean_dec_ref(v_k_748_);
lean_dec_ref(v_hyp_746_);
lean_dec_ref(v_00_u03c3s_745_);
v_a_783_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_777_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_777_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref_known(v___x_771_, 2);
lean_dec(v_a_764_);
lean_dec(v_a_759_);
lean_dec_ref(v_k_748_);
lean_dec(v_name_747_);
lean_dec_ref(v_hyp_746_);
lean_dec_ref(v_00_u03c3s_745_);
v_a_791_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_775_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_775_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
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
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_759_);
lean_dec_ref(v_k_748_);
lean_dec(v_name_747_);
lean_dec_ref(v_hyp_746_);
lean_dec_ref(v_00_u03c3s_745_);
v_a_799_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_763_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_763_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_k_748_);
lean_dec(v_name_747_);
lean_dec_ref(v_hyp_746_);
lean_dec_ref(v_00_u03c3s_745_);
v_a_807_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_758_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_758_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___boxed(lean_object* v_00_u03c3s_815_, lean_object* v_hyp_816_, lean_object* v_name_817_, lean_object* v_k_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_815_, v_hyp_816_, v_name_817_, v_k_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_858_; 
v_ks_833_ = lean_ctor_get(v_x_829_, 0);
v_vs_834_ = lean_ctor_get(v_x_829_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_858_ == 0)
{
v___x_836_ = v_x_829_;
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_vs_834_);
lean_inc(v_ks_833_);
lean_dec(v_x_829_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_array_get_size(v_ks_833_);
v___x_839_ = lean_nat_dec_lt(v_x_830_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec(v_x_830_);
v___x_840_ = lean_array_push(v_ks_833_, v_x_831_);
v___x_841_ = lean_array_push(v_vs_834_, v_x_832_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_841_);
lean_ctor_set(v___x_836_, 0, v___x_840_);
v___x_843_ = v___x_836_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v_k_x27_845_; uint8_t v___x_846_; 
v_k_x27_845_ = lean_array_fget_borrowed(v_ks_833_, v_x_830_);
v___x_846_ = l_Lean_instBEqMVarId_beq(v_x_831_, v_k_x27_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_848_; 
if (v_isShared_837_ == 0)
{
v___x_848_ = v___x_836_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_ks_833_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_vs_834_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_x_830_, v___x_849_);
lean_dec(v_x_830_);
v_x_829_ = v___x_848_;
v_x_830_ = v___x_850_;
goto _start;
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = lean_array_fset(v_ks_833_, v_x_830_, v_x_831_);
v___x_854_ = lean_array_fset(v_vs_834_, v_x_830_, v_x_832_);
lean_dec(v_x_830_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_854_);
lean_ctor_set(v___x_836_, 0, v___x_853_);
v___x_856_ = v___x_836_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(lean_object* v_n_859_, lean_object* v_k_860_, lean_object* v_v_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_n_859_, v___x_862_, v_k_860_, v_v_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(lean_object* v_x_865_, size_t v_x_866_, size_t v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_object* v_es_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v_j_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_es_870_ = lean_ctor_get(v_x_865_, 0);
v___x_871_ = ((size_t)31ULL);
v___x_872_ = lean_usize_land(v_x_866_, v___x_871_);
v_j_873_ = lean_usize_to_nat(v___x_872_);
v___x_874_ = lean_array_get_size(v_es_870_);
v___x_875_ = lean_nat_dec_lt(v_j_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec(v_j_873_);
lean_dec(v_x_869_);
lean_dec(v_x_868_);
return v_x_865_;
}
else
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_914_; 
lean_inc_ref(v_es_870_);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_x_865_, 0);
lean_dec(v_unused_915_);
v___x_877_ = v_x_865_;
v_isShared_878_ = v_isSharedCheck_914_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_x_865_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_914_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_v_879_; lean_object* v___x_880_; lean_object* v_xs_x27_881_; lean_object* v___y_883_; 
v_v_879_ = lean_array_fget(v_es_870_, v_j_873_);
v___x_880_ = lean_box(0);
v_xs_x27_881_ = lean_array_fset(v_es_870_, v_j_873_, v___x_880_);
switch(lean_obj_tag(v_v_879_))
{
case 0:
{
lean_object* v_key_888_; lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_key_888_ = lean_ctor_get(v_v_879_, 0);
v_val_889_ = lean_ctor_get(v_v_879_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_v_879_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v_v_879_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_inc(v_key_888_);
lean_dec(v_v_879_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_instBEqMVarId_beq(v_x_868_, v_key_888_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_891_);
v___x_894_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_888_, v_val_889_, v_x_868_, v_x_869_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
v___y_883_ = v___x_895_;
goto v___jp_882_;
}
else
{
lean_object* v___x_897_; 
lean_dec(v_val_889_);
lean_dec(v_key_888_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_x_869_);
lean_ctor_set(v___x_891_, 0, v_x_868_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_x_868_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_x_869_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
v___y_883_ = v___x_897_;
goto v___jp_882_;
}
}
}
}
case 1:
{
lean_object* v_node_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_node_900_ = lean_ctor_get(v_v_879_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v_v_879_);
if (v_isSharedCheck_912_ == 0)
{
v___x_902_ = v_v_879_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_node_900_);
lean_dec(v_v_879_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_904_ = ((size_t)5ULL);
v___x_905_ = lean_usize_shift_right(v_x_866_, v___x_904_);
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_x_867_, v___x_906_);
v___x_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_node_900_, v___x_905_, v___x_907_, v_x_868_, v_x_869_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_908_);
v___x_910_ = v___x_902_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v___y_883_ = v___x_910_;
goto v___jp_882_;
}
}
}
default: 
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_x_868_);
lean_ctor_set(v___x_913_, 1, v_x_869_);
v___y_883_ = v___x_913_;
goto v___jp_882_;
}
}
v___jp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_array_fset(v_xs_x27_881_, v_j_873_, v___y_883_);
lean_dec(v_j_873_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_884_);
v___x_886_ = v___x_877_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
else
{
lean_object* v_ks_916_; lean_object* v_vs_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_935_; 
v_ks_916_ = lean_ctor_get(v_x_865_, 0);
v_vs_917_ = lean_ctor_get(v_x_865_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_935_ == 0)
{
v___x_919_ = v_x_865_;
v_isShared_920_ = v_isSharedCheck_935_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_vs_917_);
lean_inc(v_ks_916_);
lean_dec(v_x_865_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_935_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_ks_916_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_vs_917_);
v___x_922_ = v_reuseFailAlloc_934_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v_newNode_923_; size_t v___x_924_; uint8_t v___x_925_; 
v_newNode_923_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v___x_922_, v_x_868_, v_x_869_);
v___x_924_ = ((size_t)7ULL);
v___x_925_ = lean_usize_dec_le(v___x_924_, v_x_867_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_923_);
v___x_927_ = lean_unsigned_to_nat(4u);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
lean_dec(v___x_926_);
if (v___x_928_ == 0)
{
lean_object* v_ks_929_; lean_object* v_vs_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_ks_929_ = lean_ctor_get(v_newNode_923_, 0);
lean_inc_ref(v_ks_929_);
v_vs_930_ = lean_ctor_get(v_newNode_923_, 1);
lean_inc_ref(v_vs_930_);
lean_dec_ref(v_newNode_923_);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_x_867_, v_ks_929_, v_vs_930_, v___x_931_, v___x_932_);
lean_dec_ref(v_vs_930_);
lean_dec_ref(v_ks_929_);
return v___x_933_;
}
else
{
return v_newNode_923_;
}
}
else
{
return v_newNode_923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(size_t v_depth_936_, lean_object* v_keys_937_, lean_object* v_vals_938_, lean_object* v_i_939_, lean_object* v_entries_940_){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = lean_array_get_size(v_keys_937_);
v___x_942_ = lean_nat_dec_lt(v_i_939_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec(v_i_939_);
return v_entries_940_;
}
else
{
lean_object* v_k_943_; lean_object* v_v_944_; uint64_t v___x_945_; size_t v_h_946_; size_t v___x_947_; lean_object* v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; size_t v_h_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_k_943_ = lean_array_fget_borrowed(v_keys_937_, v_i_939_);
v_v_944_ = lean_array_fget_borrowed(v_vals_938_, v_i_939_);
v___x_945_ = l_Lean_instHashableMVarId_hash(v_k_943_);
v_h_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = ((size_t)5ULL);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_sub(v_depth_936_, v___x_949_);
v___x_951_ = lean_usize_mul(v___x_947_, v___x_950_);
v_h_952_ = lean_usize_shift_right(v_h_946_, v___x_951_);
v___x_953_ = lean_nat_add(v_i_939_, v___x_948_);
lean_dec(v_i_939_);
lean_inc(v_v_944_);
lean_inc(v_k_943_);
v___x_954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_entries_940_, v_h_952_, v_depth_936_, v_k_943_, v_v_944_);
v_i_939_ = v___x_953_;
v_entries_940_ = v___x_954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_i_959_, lean_object* v_entries_960_){
_start:
{
size_t v_depth_boxed_961_; lean_object* v_res_962_; 
v_depth_boxed_961_ = lean_unbox_usize(v_depth_956_);
lean_dec(v_depth_956_);
v_res_962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_boxed_961_, v_keys_957_, v_vals_958_, v_i_959_, v_entries_960_);
lean_dec_ref(v_vals_958_);
lean_dec_ref(v_keys_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
size_t v_x_9828__boxed_968_; size_t v_x_9829__boxed_969_; lean_object* v_res_970_; 
v_x_9828__boxed_968_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_x_9829__boxed_969_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_res_970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_963_, v_x_9828__boxed_968_, v_x_9829__boxed_969_, v_x_966_, v_x_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
uint64_t v___x_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_974_ = l_Lean_instHashableMVarId_hash(v_x_972_);
v___x_975_ = lean_uint64_to_usize(v___x_974_);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_971_, v___x_975_, v___x_976_, v_x_972_, v_x_973_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(lean_object* v_mvarId_978_, lean_object* v_val_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_mctx_983_; lean_object* v_cache_984_; lean_object* v_zetaDeltaFVarIds_985_; lean_object* v_postponed_986_; lean_object* v_diag_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1016_; 
v___x_982_ = lean_st_ref_take(v___y_980_);
v_mctx_983_ = lean_ctor_get(v___x_982_, 0);
v_cache_984_ = lean_ctor_get(v___x_982_, 1);
v_zetaDeltaFVarIds_985_ = lean_ctor_get(v___x_982_, 2);
v_postponed_986_ = lean_ctor_get(v___x_982_, 3);
v_diag_987_ = lean_ctor_get(v___x_982_, 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_989_ = v___x_982_;
v_isShared_990_ = v_isSharedCheck_1016_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_diag_987_);
lean_inc(v_postponed_986_);
lean_inc(v_zetaDeltaFVarIds_985_);
lean_inc(v_cache_984_);
lean_inc(v_mctx_983_);
lean_dec(v___x_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1016_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_depth_991_; lean_object* v_levelAssignDepth_992_; lean_object* v_lmvarCounter_993_; lean_object* v_mvarCounter_994_; lean_object* v_lDecls_995_; lean_object* v_decls_996_; lean_object* v_userNames_997_; lean_object* v_lAssignment_998_; lean_object* v_eAssignment_999_; lean_object* v_dAssignment_1000_; lean_object* v_instanceTypedMVars_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1015_; 
v_depth_991_ = lean_ctor_get(v_mctx_983_, 0);
v_levelAssignDepth_992_ = lean_ctor_get(v_mctx_983_, 1);
v_lmvarCounter_993_ = lean_ctor_get(v_mctx_983_, 2);
v_mvarCounter_994_ = lean_ctor_get(v_mctx_983_, 3);
v_lDecls_995_ = lean_ctor_get(v_mctx_983_, 4);
v_decls_996_ = lean_ctor_get(v_mctx_983_, 5);
v_userNames_997_ = lean_ctor_get(v_mctx_983_, 6);
v_lAssignment_998_ = lean_ctor_get(v_mctx_983_, 7);
v_eAssignment_999_ = lean_ctor_get(v_mctx_983_, 8);
v_dAssignment_1000_ = lean_ctor_get(v_mctx_983_, 9);
v_instanceTypedMVars_1001_ = lean_ctor_get(v_mctx_983_, 10);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_mctx_983_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1003_ = v_mctx_983_;
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_instanceTypedMVars_1001_);
lean_inc(v_dAssignment_1000_);
lean_inc(v_eAssignment_999_);
lean_inc(v_lAssignment_998_);
lean_inc(v_userNames_997_);
lean_inc(v_decls_996_);
lean_inc(v_lDecls_995_);
lean_inc(v_mvarCounter_994_);
lean_inc(v_lmvarCounter_993_);
lean_inc(v_levelAssignDepth_992_);
lean_inc(v_depth_991_);
lean_dec(v_mctx_983_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_999_, v_mvarId_978_, v_val_979_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 8, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_depth_991_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_levelAssignDepth_992_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_lmvarCounter_993_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_mvarCounter_994_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v_lDecls_995_);
lean_ctor_set(v_reuseFailAlloc_1014_, 5, v_decls_996_);
lean_ctor_set(v_reuseFailAlloc_1014_, 6, v_userNames_997_);
lean_ctor_set(v_reuseFailAlloc_1014_, 7, v_lAssignment_998_);
lean_ctor_set(v_reuseFailAlloc_1014_, 8, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1014_, 9, v_dAssignment_1000_);
lean_ctor_set(v_reuseFailAlloc_1014_, 10, v_instanceTypedMVars_1001_);
v___x_1007_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1007_);
v___x_1009_ = v___x_989_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_cache_984_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_zetaDeltaFVarIds_985_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_postponed_986_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_diag_987_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_st_ref_put(v___y_980_, v___x_1009_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg___boxed(lean_object* v_mvarId_1017_, lean_object* v_val_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_mvarId_1017_, v_val_1018_, v___y_1019_);
lean_dec(v___y_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(lean_object* v_snd_1023_, lean_object* v_hyp_1024_, lean_object* v___x_1025_, lean_object* v_fst_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc(v_hyp_1024_);
lean_inc_ref(v_snd_1023_);
v___x_1036_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_1023_, v_hyp_1024_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v_ref_1038_; lean_object* v_00_u03c3s_1039_; lean_object* v_focusHyp_1040_; lean_object* v___f_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_n(v_a_1037_, 2);
lean_dec_ref_known(v___x_1036_, 1);
v_ref_1038_ = lean_ctor_get(v___y_1033_, 4);
v_00_u03c3s_1039_ = lean_ctor_get(v_snd_1023_, 1);
v_focusHyp_1040_ = lean_ctor_get(v_a_1037_, 0);
lean_inc_ref(v_snd_1023_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1041_, 0, v_a_1037_);
lean_closure_set(v___f_1041_, 1, v_snd_1023_);
v___x_1042_ = 0;
v___x_1043_ = l_Lean_SourceInfo_fromRef(v_ref_1038_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0));
v___x_1045_ = l_Lean_Name_mkStr2(v___x_1025_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_1043_, v___x_1045_, v_hyp_1024_);
lean_inc_ref(v_focusHyp_1040_);
lean_inc_ref(v_00_u03c3s_1039_);
v___x_1047_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_1039_, v_focusHyp_1040_, v___x_1046_, v___f_1041_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_snd_1049_; lean_object* v_fst_1050_; lean_object* v_snd_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1063_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_snd_1049_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1049_);
v_fst_1050_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1050_);
lean_dec(v_a_1048_);
v_snd_1051_ = lean_ctor_get(v_snd_1049_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_1049_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_snd_1049_, 0);
lean_dec(v_unused_1064_);
v___x_1053_ = v_snd_1049_;
v_isShared_1054_ = v_isSharedCheck_1063_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snd_1051_);
lean_dec(v_snd_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1063_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1055_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_1037_, v_snd_1023_, v_snd_1051_);
v___x_1056_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_1026_, v___x_1055_, v___y_1032_);
lean_dec_ref(v___x_1056_);
v___x_1057_ = l_Lean_Expr_mvarId_x21(v_fst_1050_);
lean_dec(v_fst_1050_);
v___x_1058_ = lean_box(0);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 1, v___x_1058_);
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1060_ = v___x_1053_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1060_, v___y_1028_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_a_1037_);
lean_dec(v_fst_1026_);
lean_dec_ref(v_snd_1023_);
v_a_1065_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1047_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1047_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_fst_1026_);
lean_dec_ref(v___x_1025_);
lean_dec(v_hyp_1024_);
lean_dec_ref(v_snd_1023_);
v_a_1073_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1036_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1036_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed(lean_object* v_snd_1081_, lean_object* v_hyp_1082_, lean_object* v___x_1083_, lean_object* v_fst_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(v_snd_1081_, v_hyp_1082_, v___x_1083_, v_fst_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0));
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3));
lean_inc(v_x_1103_);
v___x_1115_ = l_Lean_Syntax_isOfKind(v_x_1103_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec(v_x_1103_);
v___x_1116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1105_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; lean_object* v_hyp_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_fst_1119_ = lean_ctor_get(v_a_1118_, 0);
lean_inc_n(v_fst_1119_, 2);
v_snd_1120_ = lean_ctor_get(v_a_1118_, 1);
lean_inc(v_snd_1120_);
lean_dec(v_a_1118_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v_hyp_1122_ = l_Lean_Syntax_getArg(v_x_1103_, v___x_1121_);
lean_dec(v_x_1103_);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1123_, 0, v_snd_1120_);
lean_closure_set(v___f_1123_, 1, v_hyp_1122_);
lean_closure_set(v___f_1123_, 2, v___x_1113_);
lean_closure_set(v___f_1123_, 3, v_fst_1119_);
v___x_1124_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_1119_, v___f_1123_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
return v___x_1124_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_x_1103_);
v_a_1125_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1117_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1117_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed(lean_object* v_x_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(v_x_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03c3s_1145_, lean_object* v_hyp_1146_, lean_object* v_name_1147_, lean_object* v_k_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_1145_, v_hyp_1146_, v_name_1147_, v_k_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03c3s_1160_, lean_object* v_hyp_1161_, lean_object* v_name_1162_, lean_object* v_k_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(v_00_u03b1_1159_, v_00_u03c3s_1160_, v_hyp_1161_, v_name_1162_, v_k_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(lean_object* v_mvarId_1174_, lean_object* v_val_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_mvarId_1174_, v_val_1175_, v___y_1181_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___boxed(lean_object* v_mvarId_1186_, lean_object* v_val_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(v_mvarId_1186_, v_val_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(lean_object* v_00_u03b1_1198_, lean_object* v_name_1199_, uint8_t v_bi_1200_, lean_object* v_type_1201_, lean_object* v_k_1202_, uint8_t v_kind_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_1199_, v_bi_1200_, v_type_1201_, v_k_1202_, v_kind_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_name_1215_, lean_object* v_bi_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, lean_object* v_kind_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v_bi_boxed_1229_; uint8_t v_kind_boxed_1230_; lean_object* v_res_1231_; 
v_bi_boxed_1229_ = lean_unbox(v_bi_1216_);
v_kind_boxed_1230_ = lean_unbox(v_kind_1219_);
v_res_1231_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(v_00_u03b1_1214_, v_name_1215_, v_bi_boxed_1229_, v_type_1217_, v_k_1218_, v_kind_boxed_1230_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(lean_object* v_00_u03b1_1232_, lean_object* v_name_1233_, lean_object* v_type_1234_, lean_object* v_k_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_1233_, v_type_1234_, v_k_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_name_1247_, lean_object* v_type_1248_, lean_object* v_k_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(v_00_u03b1_1246_, v_name_1247_, v_type_1248_, v_k_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_x_1261_, v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, size_t v_x_1267_, size_t v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_1266_, v_x_1267_, v_x_1268_, v_x_1269_, v_x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
size_t v_x_10357__boxed_1278_; size_t v_x_10358__boxed_1279_; lean_object* v_res_1280_; 
v_x_10357__boxed_1278_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_x_10358__boxed_1279_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_res_1280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(v_00_u03b2_1272_, v_x_1273_, v_x_10357__boxed_1278_, v_x_10358__boxed_1279_, v_x_1276_, v_x_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_1281_, lean_object* v_n_1282_, lean_object* v_k_1283_, lean_object* v_v_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v_n_1282_, v_k_1283_, v_v_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1286_, size_t v_depth_1287_, lean_object* v_keys_1288_, lean_object* v_vals_1289_, lean_object* v_heq_1290_, lean_object* v_i_1291_, lean_object* v_entries_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_1287_, v_keys_1288_, v_vals_1289_, v_i_1291_, v_entries_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_depth_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_entries_1300_){
_start:
{
size_t v_depth_boxed_1301_; lean_object* v_res_1302_; 
v_depth_boxed_1301_ = lean_unbox_usize(v_depth_1295_);
lean_dec(v_depth_1295_);
v_res_1302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_1294_, v_depth_boxed_1301_, v_keys_1296_, v_vals_1297_, v_heq_1298_, v_i_1299_, v_entries_1300_);
lean_dec_ref(v_vals_1297_);
lean_dec_ref(v_keys_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_x_1304_, v_x_1305_, v_x_1306_, v_x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1(){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1320_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3));
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3));
v___x_1323_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed), 10, 0);
v___x_1324_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1320_, v___x_1321_, v___x_1322_, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___boxed(lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0(lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v___x_1332_, lean_object* v_00_u03c3s_1333_, lean_object* v_hyps_1334_, lean_object* v_target_1335_, lean_object* v_00_u03c6_1336_, lean_object* v_inst_1337_, lean_object* v_toPure_1338_, lean_object* v_____x_1339_){
_start:
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1354_; 
v_fst_1340_ = lean_ctor_get(v_____x_1339_, 0);
v_snd_1341_ = lean_ctor_get(v_____x_1339_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_____x_1339_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1343_ = v_____x_1339_;
v_isShared_1344_ = v_isSharedCheck_1354_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_____x_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1354_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_prf_1349_; lean_object* v___x_1351_; 
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0));
v___x_1347_ = l_Lean_Name_mkStr6(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1331_, v___x_1345_, v___x_1346_);
v___x_1348_ = l_Lean_mkConst(v___x_1347_, v___x_1332_);
v_prf_1349_ = l_Lean_mkApp6(v___x_1348_, v_00_u03c3s_1333_, v_hyps_1334_, v_target_1335_, v_00_u03c6_1336_, v_inst_1337_, v_snd_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_prf_1349_);
v___x_1351_ = v___x_1343_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_fst_1340_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_prf_1349_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_apply_2(v_toPure_1338_, lean_box(0), v___x_1351_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1(lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_00_u03c3s_1360_, lean_object* v_hyps_1361_, lean_object* v_target_1362_, lean_object* v_00_u03c6_1363_, lean_object* v_toPure_1364_, lean_object* v_k_1365_, lean_object* v_toBind_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_inc_ref(v_00_u03c6_1363_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0), 12, 11);
lean_closure_set(v___f_1368_, 0, v___x_1355_);
lean_closure_set(v___f_1368_, 1, v___x_1356_);
lean_closure_set(v___f_1368_, 2, v___x_1357_);
lean_closure_set(v___f_1368_, 3, v___x_1358_);
lean_closure_set(v___f_1368_, 4, v___x_1359_);
lean_closure_set(v___f_1368_, 5, v_00_u03c3s_1360_);
lean_closure_set(v___f_1368_, 6, v_hyps_1361_);
lean_closure_set(v___f_1368_, 7, v_target_1362_);
lean_closure_set(v___f_1368_, 8, v_00_u03c6_1363_);
lean_closure_set(v___f_1368_, 9, v_inst_1367_);
lean_closure_set(v___f_1368_, 10, v_toPure_1364_);
v___x_1369_ = lean_apply_1(v_k_1365_, v_00_u03c6_1363_);
v___x_1370_ = lean_apply_4(v_toBind_1366_, lean_box(0), lean_box(0), v___x_1369_, v___f_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2(lean_object* v_goal_1371_, lean_object* v_toPure_1372_, lean_object* v_k_1373_, lean_object* v_toBind_1374_, lean_object* v_inst_1375_, lean_object* v_00_u03c6_1376_){
_start:
{
lean_object* v_u_1377_; lean_object* v_00_u03c3s_1378_; lean_object* v_hyps_1379_; lean_object* v_target_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_u_1377_ = lean_ctor_get(v_goal_1371_, 0);
lean_inc(v_u_1377_);
v_00_u03c3s_1378_ = lean_ctor_get(v_goal_1371_, 1);
lean_inc_ref_n(v_00_u03c3s_1378_, 2);
v_hyps_1379_ = lean_ctor_get(v_goal_1371_, 2);
lean_inc_ref(v_hyps_1379_);
v_target_1380_ = lean_ctor_get(v_goal_1371_, 3);
lean_inc_ref_n(v_target_1380_, 2);
lean_dec_ref(v_goal_1371_);
v___x_1381_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_u_1377_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
lean_inc(v_toBind_1374_);
lean_inc_ref(v_00_u03c6_1376_);
lean_inc_ref(v___x_1387_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1), 13, 12);
lean_closure_set(v___f_1388_, 0, v___x_1381_);
lean_closure_set(v___f_1388_, 1, v___x_1382_);
lean_closure_set(v___f_1388_, 2, v___x_1383_);
lean_closure_set(v___f_1388_, 3, v___x_1384_);
lean_closure_set(v___f_1388_, 4, v___x_1387_);
lean_closure_set(v___f_1388_, 5, v_00_u03c3s_1378_);
lean_closure_set(v___f_1388_, 6, v_hyps_1379_);
lean_closure_set(v___f_1388_, 7, v_target_1380_);
lean_closure_set(v___f_1388_, 8, v_00_u03c6_1376_);
lean_closure_set(v___f_1388_, 9, v_toPure_1372_);
lean_closure_set(v___f_1388_, 10, v_k_1373_);
lean_closure_set(v___f_1388_, 11, v_toBind_1374_);
v___x_1389_ = l_Lean_mkConst(v___x_1385_, v___x_1387_);
v___x_1390_ = l_Lean_mkApp3(v___x_1389_, v_00_u03c3s_1378_, v_target_1380_, v_00_u03c6_1376_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance___boxed), 7, 2);
lean_closure_set(v___x_1392_, 0, v___x_1390_);
lean_closure_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_apply_2(v_inst_1375_, lean_box(0), v___x_1392_);
v___x_1394_ = lean_apply_4(v_toBind_1374_, lean_box(0), lean_box(0), v___x_1393_, v___f_1388_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_goal_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v_toApplicative_1399_; lean_object* v_toBind_1400_; lean_object* v_toPure_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v_toApplicative_1399_ = lean_ctor_get(v_inst_1395_, 0);
lean_inc_ref(v_toApplicative_1399_);
v_toBind_1400_ = lean_ctor_get(v_inst_1395_, 1);
lean_inc_n(v_toBind_1400_, 2);
lean_dec_ref(v_inst_1395_);
v_toPure_1401_ = lean_ctor_get(v_toApplicative_1399_, 1);
lean_inc(v_toPure_1401_);
lean_dec_ref(v_toApplicative_1399_);
v___x_1402_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2);
lean_inc(v_inst_1396_);
v___x_1403_ = lean_apply_2(v_inst_1396_, lean_box(0), v___x_1402_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1404_, 0, v_goal_1397_);
lean_closure_set(v___f_1404_, 1, v_toPure_1401_);
lean_closure_set(v___f_1404_, 2, v_k_1398_);
lean_closure_set(v___f_1404_, 3, v_toBind_1400_);
lean_closure_set(v___f_1404_, 4, v_inst_1396_);
v___x_1405_ = lean_apply_4(v_toBind_1400_, lean_box(0), lean_box(0), v___x_1403_, v___f_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore(lean_object* v_m_1406_, lean_object* v_00_u03b1_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_goal_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(v_inst_1408_, v_inst_1409_, v_goal_1410_, v_k_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(lean_object* v_goal_1420_, lean_object* v_k_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_1432_ = 0;
v___x_1433_ = lean_box(0);
v___x_1434_ = l_Lean_Meta_mkFreshExprMVar(v___x_1431_, v___x_1432_, v___x_1433_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_u_1436_; lean_object* v_00_u03c3s_1437_; lean_object* v_hyps_1438_; lean_object* v_target_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_n(v_a_1435_, 2);
lean_dec_ref_known(v___x_1434_, 1);
v_u_1436_ = lean_ctor_get(v_goal_1420_, 0);
lean_inc(v_u_1436_);
v_00_u03c3s_1437_ = lean_ctor_get(v_goal_1420_, 1);
lean_inc_ref_n(v_00_u03c3s_1437_, 2);
v_hyps_1438_ = lean_ctor_get(v_goal_1420_, 2);
lean_inc_ref(v_hyps_1438_);
v_target_1439_ = lean_ctor_get(v_goal_1420_, 3);
lean_inc_ref_n(v_target_1439_, 2);
lean_dec_ref(v_goal_1420_);
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_u_1436_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
lean_inc_ref(v___x_1442_);
v___x_1443_ = l_Lean_mkConst(v___x_1440_, v___x_1442_);
v___x_1444_ = l_Lean_mkApp3(v___x_1443_, v_00_u03c3s_1437_, v_target_1439_, v_a_1435_);
v___x_1445_ = lean_box(0);
v___x_1446_ = l_Lean_Meta_synthInstance(v___x_1444_, v___x_1445_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v___y_1422_);
lean_inc(v_a_1435_);
v___x_1448_ = lean_apply_10(v_k_1421_, v_a_1435_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, lean_box(0));
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1468_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; lean_object* v_snd_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1467_; 
v_fst_1453_ = lean_ctor_get(v_a_1449_, 0);
v_snd_1454_ = lean_ctor_get(v_a_1449_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_a_1449_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1456_ = v_a_1449_;
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_snd_1454_);
lean_inc(v_fst_1453_);
lean_dec(v_a_1449_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_prf_1460_; lean_object* v___x_1462_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0));
v___x_1459_ = l_Lean_mkConst(v___x_1458_, v___x_1442_);
v_prf_1460_ = l_Lean_mkApp6(v___x_1459_, v_00_u03c3s_1437_, v_hyps_1438_, v_target_1439_, v_a_1435_, v_a_1447_, v_snd_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 1, v_prf_1460_);
v___x_1462_ = v___x_1456_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_fst_1453_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_prf_1460_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1462_);
v___x_1464_ = v___x_1451_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_dec(v_a_1447_);
lean_dec_ref_known(v___x_1442_, 2);
lean_dec_ref(v_target_1439_);
lean_dec_ref(v_hyps_1438_);
lean_dec_ref(v_00_u03c3s_1437_);
lean_dec(v_a_1435_);
return v___x_1448_;
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref_known(v___x_1442_, 2);
lean_dec_ref(v_target_1439_);
lean_dec_ref(v_hyps_1438_);
lean_dec_ref(v_00_u03c3s_1437_);
lean_dec(v_a_1435_);
lean_dec_ref(v_k_1421_);
v_a_1469_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1446_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1446_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_k_1421_);
lean_dec_ref(v_goal_1420_);
v_a_1477_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1434_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1434_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___boxed(lean_object* v_goal_1485_, lean_object* v_k_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_1485_, v_k_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(lean_object* v_00_u03b1_1497_, lean_object* v_goal_1498_, lean_object* v_k_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_1498_, v_k_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_goal_1511_, lean_object* v_k_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(v_00_u03b1_1510_, v_goal_1511_, v_k_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(lean_object* v_fst_1523_, lean_object* v_00_u03c6_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_MVarId_getTag(v_fst_1523_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_00_u03c6_1524_, v_a_1535_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = l_Lean_Expr_mvarId_x21(v_a_1537_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1536_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1536_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_00_u03c6_1524_);
v_a_1555_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1534_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1534_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed(lean_object* v_fst_1563_, lean_object* v_00_u03c6_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(v_fst_1563_, v_00_u03c6_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(lean_object* v_snd_1575_, lean_object* v___f_1576_, lean_object* v_fst_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_snd_1575_, v___f_1576_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_fst_1589_ = lean_ctor_get(v_a_1588_, 0);
v_snd_1590_ = lean_ctor_get(v_a_1588_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v_a_1588_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snd_1590_);
lean_inc(v_fst_1589_);
lean_dec(v_a_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_1577_, v_snd_1590_, v___y_1583_);
lean_dec_ref(v___x_1594_);
v___x_1595_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 1, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_fst_1589_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1597_, v___y_1579_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_fst_1577_);
v_a_1601_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1587_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1587_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed(lean_object* v_snd_1609_, lean_object* v___f_1610_, lean_object* v_fst_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(v_snd_1609_, v___f_1610_, v_fst_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(lean_object* v_x_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1));
v___x_1639_ = l_Lean_Syntax_isOfKind(v_x_1628_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1630_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___f_1645_; lean_object* v___f_1646_; lean_object* v___x_1647_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_fst_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc_n(v_fst_1643_, 3);
v_snd_1644_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_snd_1644_);
lean_dec(v_a_1642_);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1645_, 0, v_fst_1643_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1646_, 0, v_snd_1644_);
lean_closure_set(v___f_1646_, 1, v___f_1645_);
lean_closure_set(v___f_1646_, 2, v_fst_1643_);
v___x_1647_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_1643_, v___f_1646_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
return v___x_1647_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1641_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1641_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed(lean_object* v_x_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(v_x_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1(){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1676_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1));
v___x_1678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1));
v___x_1679_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed), 10, 0);
v___x_1680_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1676_, v___x_1677_, v___x_1678_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___boxed(lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
return v_res_1682_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5(void){
_start:
{
lean_object* v___x_1694_; lean_object* v_dummy_1695_; 
v___x_1694_ = lean_box(0);
v_dummy_1695_ = l_Lean_Expr_sort___override(v___x_1694_);
return v_dummy_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(lean_object* v_e_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1696_, v_a_1698_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1762_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1762_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1762_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2));
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = l_Lean_Expr_isAppOfArity(v_a_1703_, v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec(v_a_1703_);
v___x_1710_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1710_);
v___x_1712_ = v___x_1705_;
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
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1714_ = l_Lean_Expr_appArg_x21(v_a_1703_);
lean_dec(v_a_1703_);
v___x_1715_ = l_Lean_Expr_getAppFn(v___x_1714_);
v___x_1716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4));
v___x_1717_ = l_Lean_Expr_isConstOf(v___x_1715_, v___x_1716_);
lean_dec_ref(v___x_1715_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_dec_ref(v___x_1714_);
v___x_1718_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1718_);
v___x_1720_ = v___x_1705_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
else
{
lean_object* v_dummy_1722_; lean_object* v_nargs_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_dummy_1722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5, &l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5);
v_nargs_1723_ = l_Lean_Expr_getAppNumArgs(v___x_1714_);
lean_inc(v_nargs_1723_);
v___x_1724_ = lean_mk_array(v_nargs_1723_, v_dummy_1722_);
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_sub(v_nargs_1723_, v___x_1725_);
lean_dec(v_nargs_1723_);
v___x_1727_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1714_, v___x_1724_, v___x_1726_);
v___x_1728_ = lean_array_get_size(v___x_1727_);
v___x_1729_ = lean_nat_dec_lt(v___x_1728_, v___x_1708_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_del_object(v___x_1705_);
v___x_1730_ = l_Lean_instInhabitedExpr;
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_array_get(v___x_1730_, v___x_1727_, v___x_1731_);
v___x_1733_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(v___x_1732_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1749_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1749_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1749_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_nat_sub(v___x_1728_, v___x_1708_);
v___x_1739_ = lean_nat_dec_eq(v_a_1734_, v___x_1738_);
lean_dec(v___x_1738_);
lean_dec(v_a_1734_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
lean_dec_ref(v___x_1727_);
v___x_1740_ = lean_box(0);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1740_);
v___x_1742_ = v___x_1736_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = lean_array_get(v___x_1730_, v___x_1727_, v___x_1725_);
lean_dec_ref(v___x_1727_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1745_);
v___x_1747_ = v___x_1736_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v___x_1727_);
v_a_1750_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1733_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1733_);
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
lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_dec_ref(v___x_1727_);
v___x_1758_ = lean_box(0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1758_);
v___x_1760_ = v___x_1705_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1702_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1702_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___boxed(lean_object* v_e_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_e_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(lean_object* v_msgData_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_env_1785_; lean_object* v___x_1786_; lean_object* v_mctx_1787_; lean_object* v_lctx_1788_; lean_object* v_options_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1784_ = lean_st_ref_get(v___y_1782_);
v_env_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc_ref(v_env_1785_);
lean_dec(v___x_1784_);
v___x_1786_ = lean_st_ref_get(v___y_1780_);
v_mctx_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc_ref(v_mctx_1787_);
lean_dec(v___x_1786_);
v_lctx_1788_ = lean_ctor_get(v___y_1779_, 2);
v_options_1789_ = lean_ctor_get(v___y_1781_, 1);
lean_inc_ref(v_options_1789_);
lean_inc_ref(v_lctx_1788_);
v___x_1790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1790_, 0, v_env_1785_);
lean_ctor_set(v___x_1790_, 1, v_mctx_1787_);
lean_ctor_set(v___x_1790_, 2, v_lctx_1788_);
lean_ctor_set(v___x_1790_, 3, v_options_1789_);
v___x_1791_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v_msgData_1778_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1___boxed(lean_object* v_msgData_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msgData_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1800_; double v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_float_of_nat(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(lean_object* v_cls_1805_, lean_object* v_msg_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_ref_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1858_; 
v_ref_1812_ = lean_ctor_get(v___y_1809_, 4);
v___x_1813_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1858_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1858_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v_traceState_1819_; lean_object* v_env_1820_; lean_object* v_nextMacroScope_1821_; lean_object* v_ngen_1822_; lean_object* v_auxDeclNGen_1823_; lean_object* v_cache_1824_; lean_object* v_messages_1825_; lean_object* v_infoState_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1857_; 
v___x_1818_ = lean_st_ref_take(v___y_1810_);
v_traceState_1819_ = lean_ctor_get(v___x_1818_, 4);
v_env_1820_ = lean_ctor_get(v___x_1818_, 0);
v_nextMacroScope_1821_ = lean_ctor_get(v___x_1818_, 1);
v_ngen_1822_ = lean_ctor_get(v___x_1818_, 2);
v_auxDeclNGen_1823_ = lean_ctor_get(v___x_1818_, 3);
v_cache_1824_ = lean_ctor_get(v___x_1818_, 5);
v_messages_1825_ = lean_ctor_get(v___x_1818_, 6);
v_infoState_1826_ = lean_ctor_get(v___x_1818_, 7);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1818_, 8);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1829_ = v___x_1818_;
v_isShared_1830_ = v_isSharedCheck_1857_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1826_);
lean_inc(v_messages_1825_);
lean_inc(v_cache_1824_);
lean_inc(v_traceState_1819_);
lean_inc(v_auxDeclNGen_1823_);
lean_inc(v_ngen_1822_);
lean_inc(v_nextMacroScope_1821_);
lean_inc(v_env_1820_);
lean_dec(v___x_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1857_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
uint64_t v_tid_1831_; lean_object* v_traces_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1856_; 
v_tid_1831_ = lean_ctor_get_uint64(v_traceState_1819_, sizeof(void*)*1);
v_traces_1832_ = lean_ctor_get(v_traceState_1819_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_traceState_1819_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1834_ = v_traceState_1819_;
v_isShared_1835_ = v_isSharedCheck_1856_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_traces_1832_);
lean_dec(v_traceState_1819_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1856_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; double v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_float_once(&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
v___x_1838_ = 0;
v___x_1839_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1));
v___x_1840_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1840_, 0, v_cls_1805_);
lean_ctor_set(v___x_1840_, 1, v___x_1836_);
lean_ctor_set(v___x_1840_, 2, v___x_1839_);
lean_ctor_set_float(v___x_1840_, sizeof(void*)*3, v___x_1837_);
lean_ctor_set_float(v___x_1840_, sizeof(void*)*3 + 8, v___x_1837_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*3 + 16, v___x_1838_);
v___x_1841_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2));
v___x_1842_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v_a_1814_);
lean_ctor_set(v___x_1842_, 2, v___x_1841_);
lean_inc(v_ref_1812_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_ref_1812_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_PersistentArray_push___redArg(v_traces_1832_, v___x_1843_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1844_);
v___x_1846_ = v___x_1834_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1844_);
lean_ctor_set_uint64(v_reuseFailAlloc_1855_, sizeof(void*)*1, v_tid_1831_);
v___x_1846_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 4, v___x_1846_);
v___x_1848_ = v___x_1829_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_env_1820_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_nextMacroScope_1821_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_ngen_1822_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_auxDeclNGen_1823_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1854_, 5, v_cache_1824_);
lean_ctor_set(v_reuseFailAlloc_1854_, 6, v_messages_1825_);
lean_ctor_set(v_reuseFailAlloc_1854_, 7, v_infoState_1826_);
lean_ctor_set(v_reuseFailAlloc_1854_, 8, v_snapshotTasks_1827_);
v___x_1848_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_st_ref_put(v___y_1810_, v___x_1848_);
v___x_1850_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1850_);
v___x_1852_ = v___x_1816_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___boxed(lean_object* v_cls_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(v_cls_1859_, v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(lean_object* v_mvarId_1867_, lean_object* v_val_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v_cache_1873_; lean_object* v_zetaDeltaFVarIds_1874_; lean_object* v_postponed_1875_; lean_object* v_diag_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1905_; 
v___x_1871_ = lean_st_ref_take(v___y_1869_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
v_cache_1873_ = lean_ctor_get(v___x_1871_, 1);
v_zetaDeltaFVarIds_1874_ = lean_ctor_get(v___x_1871_, 2);
v_postponed_1875_ = lean_ctor_get(v___x_1871_, 3);
v_diag_1876_ = lean_ctor_get(v___x_1871_, 4);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1878_ = v___x_1871_;
v_isShared_1879_ = v_isSharedCheck_1905_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_diag_1876_);
lean_inc(v_postponed_1875_);
lean_inc(v_zetaDeltaFVarIds_1874_);
lean_inc(v_cache_1873_);
lean_inc(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1905_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_depth_1880_; lean_object* v_levelAssignDepth_1881_; lean_object* v_lmvarCounter_1882_; lean_object* v_mvarCounter_1883_; lean_object* v_lDecls_1884_; lean_object* v_decls_1885_; lean_object* v_userNames_1886_; lean_object* v_lAssignment_1887_; lean_object* v_eAssignment_1888_; lean_object* v_dAssignment_1889_; lean_object* v_instanceTypedMVars_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1904_; 
v_depth_1880_ = lean_ctor_get(v_mctx_1872_, 0);
v_levelAssignDepth_1881_ = lean_ctor_get(v_mctx_1872_, 1);
v_lmvarCounter_1882_ = lean_ctor_get(v_mctx_1872_, 2);
v_mvarCounter_1883_ = lean_ctor_get(v_mctx_1872_, 3);
v_lDecls_1884_ = lean_ctor_get(v_mctx_1872_, 4);
v_decls_1885_ = lean_ctor_get(v_mctx_1872_, 5);
v_userNames_1886_ = lean_ctor_get(v_mctx_1872_, 6);
v_lAssignment_1887_ = lean_ctor_get(v_mctx_1872_, 7);
v_eAssignment_1888_ = lean_ctor_get(v_mctx_1872_, 8);
v_dAssignment_1889_ = lean_ctor_get(v_mctx_1872_, 9);
v_instanceTypedMVars_1890_ = lean_ctor_get(v_mctx_1872_, 10);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_mctx_1872_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1892_ = v_mctx_1872_;
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_instanceTypedMVars_1890_);
lean_inc(v_dAssignment_1889_);
lean_inc(v_eAssignment_1888_);
lean_inc(v_lAssignment_1887_);
lean_inc(v_userNames_1886_);
lean_inc(v_decls_1885_);
lean_inc(v_lDecls_1884_);
lean_inc(v_mvarCounter_1883_);
lean_inc(v_lmvarCounter_1882_);
lean_inc(v_levelAssignDepth_1881_);
lean_inc(v_depth_1880_);
lean_dec(v_mctx_1872_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_1888_, v_mvarId_1867_, v_val_1868_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 8, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_depth_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_levelAssignDepth_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_lmvarCounter_1882_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_mvarCounter_1883_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_lDecls_1884_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v_decls_1885_);
lean_ctor_set(v_reuseFailAlloc_1903_, 6, v_userNames_1886_);
lean_ctor_set(v_reuseFailAlloc_1903_, 7, v_lAssignment_1887_);
lean_ctor_set(v_reuseFailAlloc_1903_, 8, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1903_, 9, v_dAssignment_1889_);
lean_ctor_set(v_reuseFailAlloc_1903_, 10, v_instanceTypedMVars_1890_);
v___x_1896_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1896_);
v___x_1898_ = v___x_1878_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_cache_1873_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_zetaDeltaFVarIds_1874_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_postponed_1875_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_diag_1876_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_st_ref_put(v___y_1869_, v___x_1898_);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg___boxed(lean_object* v_mvarId_1906_, lean_object* v_val_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvarId_1906_, v_val_1907_, v___y_1908_);
lean_dec(v___y_1908_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__4));
v___x_1922_ = l_Lean_mkConst(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__6));
v___x_1928_ = l_Lean_mkConst(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___x_1939_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
v___x_1940_ = l_Lean_Name_append(v___x_1939_, v___x_1938_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__13));
v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRflAndAndIntro(lean_object* v_mvar_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v_a_2000_; lean_object* v___y_2013_; lean_object* v___x_2034_; 
lean_inc(v_mvar_1944_);
v___x_2034_ = l_Lean_MVarId_getType(v_mvar_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2035_, v_a_1946_);
v___y_2013_ = v___x_2036_;
goto v___jp_2012_;
}
else
{
v___y_2013_ = v___x_2034_;
goto v___jp_2012_;
}
v___jp_1950_:
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__1));
v___x_1957_ = l_Lean_Expr_isAppOf(v___y_1951_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__3));
v___x_1959_ = lean_unsigned_to_nat(2u);
v___x_1960_ = l_Lean_Expr_isAppOfArity(v___y_1951_, v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_inc(v_mvar_1944_);
v___x_1961_ = l_Lean_MVarId_setType___redArg(v_mvar_1944_, v___y_1951_, v___y_1953_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = l_Lean_MVarId_applyRfl(v_mvar_1944_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1962_;
}
else
{
lean_dec(v_mvar_1944_);
return v___x_1961_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1963_ = l_Lean_Expr_appFn_x21(v___y_1951_);
v___x_1964_ = l_Lean_Expr_appArg_x21(v___x_1963_);
lean_dec_ref(v___x_1963_);
lean_inc_ref(v___x_1964_);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
v___x_1966_ = 0;
v___x_1967_ = lean_box(0);
v___x_1968_ = l_Lean_Meta_mkFreshExprMVar(v___x_1965_, v___x_1966_, v___x_1967_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_Expr_appArg_x21(v___y_1951_);
lean_dec_ref(v___y_1951_);
lean_inc_ref(v___x_1970_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
v___x_1972_ = l_Lean_Meta_mkFreshExprMVar(v___x_1971_, v___x_1966_, v___x_1967_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1974_ = l_Lean_Expr_mvarId_x21(v_a_1969_);
v___x_1975_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_1974_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref_known(v___x_1975_, 1);
v___x_1976_ = l_Lean_Expr_mvarId_x21(v_a_1973_);
v___x_1977_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_1976_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref_known(v___x_1977_, 1);
v___x_1978_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__5, &l_Lean_MVarId_applyRflAndAndIntro___closed__5_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5);
v___x_1979_ = l_Lean_mkApp4(v___x_1978_, v___x_1964_, v___x_1970_, v_a_1969_, v_a_1973_);
v___x_1980_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_1944_, v___x_1979_, v___y_1953_);
return v___x_1980_;
}
else
{
lean_dec(v_a_1973_);
lean_dec_ref(v___x_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v___x_1964_);
lean_dec(v_mvar_1944_);
return v___x_1977_;
}
}
else
{
lean_dec(v_a_1973_);
lean_dec_ref(v___x_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v___x_1964_);
lean_dec(v_mvar_1944_);
return v___x_1975_;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v___x_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v___x_1964_);
lean_dec(v_mvar_1944_);
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v___x_1964_);
lean_dec_ref(v___y_1951_);
lean_dec(v_mvar_1944_);
v_a_1989_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1968_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1968_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec_ref(v___y_1951_);
v___x_1997_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__7, &l_Lean_MVarId_applyRflAndAndIntro___closed__7_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7);
v___x_1998_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_1944_, v___x_1997_, v___y_1953_);
return v___x_1998_;
}
}
v___jp_1999_:
{
lean_object* v_options_2001_; uint8_t v_hasTrace_2002_; 
v_options_2001_ = lean_ctor_get(v_a_1947_, 1);
v_hasTrace_2002_ = lean_ctor_get_uint8(v_options_2001_, sizeof(void*)*1);
if (v_hasTrace_2002_ == 0)
{
v___y_1951_ = v_a_2000_;
v___y_1952_ = v_a_1945_;
v___y_1953_ = v_a_1946_;
v___y_1954_ = v_a_1947_;
v___y_1955_ = v_a_1948_;
goto v___jp_1950_;
}
else
{
lean_object* v_toCold_2003_; lean_object* v_inheritedTraceOptions_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_toCold_2003_ = lean_ctor_get(v_a_1947_, 0);
v_inheritedTraceOptions_2004_ = lean_ctor_get(v_toCold_2003_, 4);
v___x_2005_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___x_2006_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__12, &l_Lean_MVarId_applyRflAndAndIntro___closed__12_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12);
v___x_2007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2004_, v_options_2001_, v___x_2006_);
if (v___x_2007_ == 0)
{
v___y_1951_ = v_a_2000_;
v___y_1952_ = v_a_1945_;
v___y_1953_ = v_a_1946_;
v___y_1954_ = v_a_1947_;
v___y_1955_ = v_a_1948_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__14, &l_Lean_MVarId_applyRflAndAndIntro___closed__14_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14);
lean_inc_ref(v_a_2000_);
v___x_2009_ = l_Lean_MessageData_ofExpr(v_a_2000_);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2008_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(v___x_2005_, v___x_2010_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
v___y_1951_ = v_a_2000_;
v___y_1952_ = v_a_1945_;
v___y_1953_ = v_a_1946_;
v___y_1954_ = v_a_1947_;
v___y_1955_ = v_a_1948_;
goto v___jp_1950_;
}
else
{
lean_dec_ref(v_a_2000_);
lean_dec(v_mvar_1944_);
return v___x_2011_;
}
}
}
}
v___jp_2012_:
{
if (lean_obj_tag(v___y_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___y_2013_, 0);
lean_inc_n(v_a_2014_, 2);
lean_dec_ref_known(v___y_2013_, 1);
v___x_2015_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_a_2014_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
if (lean_obj_tag(v_a_2016_) == 0)
{
v_a_2000_ = v_a_2014_;
goto v___jp_1999_;
}
else
{
lean_object* v_val_2017_; 
lean_dec(v_a_2014_);
v_val_2017_ = lean_ctor_get(v_a_2016_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v_a_2016_, 1);
v_a_2000_ = v_val_2017_;
goto v___jp_1999_;
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_a_2014_);
lean_dec(v_mvar_1944_);
v_a_2018_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2015_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2015_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_mvar_1944_);
v_a_2026_ = lean_ctor_get(v___y_2013_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___y_2013_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___y_2013_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___y_2013_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRflAndAndIntro___boxed(lean_object* v_mvar_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_MVarId_applyRflAndAndIntro(v_mvar_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(lean_object* v_mvarId_2044_, lean_object* v_val_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvarId_2044_, v_val_2045_, v___y_2047_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___boxed(lean_object* v_mvarId_2052_, lean_object* v_val_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(v_mvarId_2052_, v_val_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(lean_object* v_goal_2060_, lean_object* v_k_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_2068_ = 0;
v___x_2069_ = lean_box(0);
v___x_2070_ = l_Lean_Meta_mkFreshExprMVar(v___x_2067_, v___x_2068_, v___x_2069_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v_u_2072_; lean_object* v_00_u03c3s_2073_; lean_object* v_hyps_2074_; lean_object* v_target_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_n(v_a_2071_, 2);
lean_dec_ref_known(v___x_2070_, 1);
v_u_2072_ = lean_ctor_get(v_goal_2060_, 0);
lean_inc(v_u_2072_);
v_00_u03c3s_2073_ = lean_ctor_get(v_goal_2060_, 1);
lean_inc_ref_n(v_00_u03c3s_2073_, 2);
v_hyps_2074_ = lean_ctor_get(v_goal_2060_, 2);
lean_inc_ref(v_hyps_2074_);
v_target_2075_ = lean_ctor_get(v_goal_2060_, 3);
lean_inc_ref_n(v_target_2075_, 2);
lean_dec_ref(v_goal_2060_);
v___x_2076_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_u_2072_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
lean_inc_ref(v___x_2078_);
v___x_2079_ = l_Lean_mkConst(v___x_2076_, v___x_2078_);
v___x_2080_ = l_Lean_mkApp3(v___x_2079_, v_00_u03c3s_2073_, v_target_2075_, v_a_2071_);
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Lean_Meta_synthInstance(v___x_2080_, v___x_2081_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
lean_inc(v___y_2063_);
lean_inc_ref(v___y_2062_);
lean_inc(v_a_2071_);
v___x_2084_ = lean_apply_6(v_k_2061_, v_a_2071_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, lean_box(0));
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
if (lean_obj_tag(v_a_2085_) == 0)
{
lean_dec(v_a_2083_);
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_target_2075_);
lean_dec_ref(v_hyps_2074_);
lean_dec_ref(v_00_u03c3s_2073_);
lean_dec(v_a_2071_);
return v___x_2084_;
}
else
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2112_; 
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2113_);
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2112_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2112_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2111_; 
v_val_2089_ = lean_ctor_get(v_a_2085_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2091_ = v_a_2085_;
v_isShared_2092_ = v_isSharedCheck_2111_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_dec(v_a_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2111_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2110_; 
v_fst_2093_ = lean_ctor_get(v_val_2089_, 0);
v_snd_2094_ = lean_ctor_get(v_val_2089_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_val_2089_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2096_ = v_val_2089_;
v_isShared_2097_ = v_isSharedCheck_2110_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_inc(v_fst_2093_);
lean_dec(v_val_2089_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2110_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_prf_2100_; lean_object* v___x_2102_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0));
v___x_2099_ = l_Lean_mkConst(v___x_2098_, v___x_2078_);
v_prf_2100_ = l_Lean_mkApp6(v___x_2099_, v_00_u03c3s_2073_, v_hyps_2074_, v_target_2075_, v_a_2071_, v_a_2083_, v_snd_2094_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_prf_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_fst_2093_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_prf_2100_);
v___x_2102_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2104_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2102_);
v___x_2104_ = v___x_2091_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2104_);
v___x_2106_ = v___x_2087_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
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
lean_dec(v_a_2083_);
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_target_2075_);
lean_dec_ref(v_hyps_2074_);
lean_dec_ref(v_00_u03c3s_2073_);
lean_dec(v_a_2071_);
return v___x_2084_;
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref_known(v___x_2078_, 2);
lean_dec_ref(v_target_2075_);
lean_dec_ref(v_hyps_2074_);
lean_dec_ref(v_00_u03c3s_2073_);
lean_dec(v_a_2071_);
lean_dec_ref(v_k_2061_);
v_a_2114_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2082_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2082_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_k_2061_);
lean_dec_ref(v_goal_2060_);
v_a_2122_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2070_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2070_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg___boxed(lean_object* v_goal_2130_, lean_object* v_k_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2130_, v_k_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(lean_object* v_00_u03b1_2138_, lean_object* v_goal_2139_, lean_object* v_k_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2139_, v_k_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_goal_2148_, lean_object* v_k_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(v_00_u03b1_2147_, v_goal_2148_, v_k_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(lean_object* v_cls_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_options_2162_; uint8_t v_hasTrace_2163_; 
v_options_2162_ = lean_ctor_get(v___y_2159_, 1);
v_hasTrace_2163_ = lean_ctor_get_uint8(v_options_2162_, sizeof(void*)*1);
if (v_hasTrace_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_cls_2156_);
v___x_2164_ = lean_box(v_hasTrace_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
else
{
lean_object* v_toCold_2167_; lean_object* v_inheritedTraceOptions_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_toCold_2167_ = lean_ctor_get(v___y_2159_, 0);
v_inheritedTraceOptions_2168_ = lean_ctor_get(v_toCold_2167_, 4);
v___x_2169_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
v___x_2170_ = l_Lean_Name_append(v___x_2169_, v_cls_2156_);
v___x_2171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2168_, v_options_2162_, v___x_2170_);
lean_dec(v___x_2170_);
v___x_2172_ = lean_box(v___x_2171_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed(lean_object* v_cls_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(v_cls_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(lean_object* v_cls_2184_, lean_object* v_msg_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_ref_2191_; lean_object* v___x_2192_; lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2237_; 
v_ref_2191_ = lean_ctor_get(v___y_2188_, 4);
v___x_2192_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2237_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2237_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v_traceState_2198_; lean_object* v_env_2199_; lean_object* v_nextMacroScope_2200_; lean_object* v_ngen_2201_; lean_object* v_auxDeclNGen_2202_; lean_object* v_cache_2203_; lean_object* v_messages_2204_; lean_object* v_infoState_2205_; lean_object* v_snapshotTasks_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2236_; 
v___x_2197_ = lean_st_ref_take(v___y_2189_);
v_traceState_2198_ = lean_ctor_get(v___x_2197_, 4);
v_env_2199_ = lean_ctor_get(v___x_2197_, 0);
v_nextMacroScope_2200_ = lean_ctor_get(v___x_2197_, 1);
v_ngen_2201_ = lean_ctor_get(v___x_2197_, 2);
v_auxDeclNGen_2202_ = lean_ctor_get(v___x_2197_, 3);
v_cache_2203_ = lean_ctor_get(v___x_2197_, 5);
v_messages_2204_ = lean_ctor_get(v___x_2197_, 6);
v_infoState_2205_ = lean_ctor_get(v___x_2197_, 7);
v_snapshotTasks_2206_ = lean_ctor_get(v___x_2197_, 8);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2208_ = v___x_2197_;
v_isShared_2209_ = v_isSharedCheck_2236_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_snapshotTasks_2206_);
lean_inc(v_infoState_2205_);
lean_inc(v_messages_2204_);
lean_inc(v_cache_2203_);
lean_inc(v_traceState_2198_);
lean_inc(v_auxDeclNGen_2202_);
lean_inc(v_ngen_2201_);
lean_inc(v_nextMacroScope_2200_);
lean_inc(v_env_2199_);
lean_dec(v___x_2197_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2236_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
uint64_t v_tid_2210_; lean_object* v_traces_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2235_; 
v_tid_2210_ = lean_ctor_get_uint64(v_traceState_2198_, sizeof(void*)*1);
v_traces_2211_ = lean_ctor_get(v_traceState_2198_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_traceState_2198_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2213_ = v_traceState_2198_;
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_traces_2211_);
lean_dec(v_traceState_2198_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; double v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_float_once(&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
v___x_2217_ = 0;
v___x_2218_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1));
v___x_2219_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2219_, 0, v_cls_2184_);
lean_ctor_set(v___x_2219_, 1, v___x_2215_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
lean_ctor_set_float(v___x_2219_, sizeof(void*)*3, v___x_2216_);
lean_ctor_set_float(v___x_2219_, sizeof(void*)*3 + 8, v___x_2216_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*3 + 16, v___x_2217_);
v___x_2220_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2));
v___x_2221_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v_a_2193_);
lean_ctor_set(v___x_2221_, 2, v___x_2220_);
lean_inc(v_ref_2191_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_ref_2191_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_PersistentArray_push___redArg(v_traces_2211_, v___x_2222_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2223_);
v___x_2225_ = v___x_2213_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2223_);
lean_ctor_set_uint64(v_reuseFailAlloc_2234_, sizeof(void*)*1, v_tid_2210_);
v___x_2225_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 4, v___x_2225_);
v___x_2227_ = v___x_2208_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_env_2199_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_nextMacroScope_2200_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_ngen_2201_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_auxDeclNGen_2202_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2233_, 5, v_cache_2203_);
lean_ctor_set(v_reuseFailAlloc_2233_, 6, v_messages_2204_);
lean_ctor_set(v_reuseFailAlloc_2233_, 7, v_infoState_2205_);
lean_ctor_set(v_reuseFailAlloc_2233_, 8, v_snapshotTasks_2206_);
v___x_2227_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_st_ref_put(v___y_2189_, v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0));
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2229_);
v___x_2231_ = v___x_2195_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___boxed(lean_object* v_cls_2238_, lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2238_, v_msg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(lean_object* v___f_2252_, lean_object* v_cls_2253_, lean_object* v_00_u03c6_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___y_2261_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___x_2313_; 
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
v___x_2313_ = lean_apply_5(v___f_2252_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, lean_box(0));
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2336_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2336_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2336_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v___x_2318_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2318_);
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
else
{
lean_object* v_val_2322_; uint8_t v___x_2323_; 
lean_del_object(v___x_2316_);
v_val_2322_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_a_2314_, 1);
v___x_2323_ = lean_unbox(v_val_2322_);
lean_dec(v_val_2322_);
if (v___x_2323_ == 0)
{
v___y_2267_ = v___y_2255_;
v___y_2268_ = v___y_2256_;
v___y_2269_ = v___y_2257_;
v___y_2270_ = v___y_2258_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3);
lean_inc_ref(v_00_u03c6_2254_);
v___x_2325_ = l_Lean_MessageData_ofExpr(v_00_u03c6_2254_);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
lean_inc(v_cls_2253_);
v___x_2327_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2253_, v___x_2326_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_dec_ref_known(v___x_2327_, 1);
v___y_2267_ = v___y_2255_;
v___y_2268_ = v___y_2256_;
v___y_2269_ = v___y_2257_;
v___y_2270_ = v___y_2258_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v_a_2337_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2313_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2313_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___y_2261_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
v___jp_2266_:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_inc_ref(v_00_u03c6_2254_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_00_u03c6_2254_);
v___x_2272_ = 0;
v___x_2273_ = lean_box(0);
v___x_2274_ = l_Lean_Meta_mkFreshExprMVar(v___x_2271_, v___x_2272_, v___x_2273_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = l_Lean_Expr_mvarId_x21(v_a_2275_);
v___x_2277_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2276_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_options_2278_; uint8_t v_hasTrace_2279_; 
lean_dec_ref_known(v___x_2277_, 1);
v_options_2278_ = lean_ctor_get(v___y_2269_, 1);
v_hasTrace_2279_ = lean_ctor_get_uint8(v_options_2278_, sizeof(void*)*1);
if (v_hasTrace_2279_ == 0)
{
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v___y_2261_ = v_a_2275_;
goto v___jp_2260_;
}
else
{
lean_object* v_toCold_2280_; lean_object* v_inheritedTraceOptions_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_toCold_2280_ = lean_ctor_get(v___y_2269_, 0);
v_inheritedTraceOptions_2281_ = lean_ctor_get(v_toCold_2280_, 4);
v___x_2282_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
lean_inc(v_cls_2253_);
v___x_2283_ = l_Lean_Name_append(v___x_2282_, v_cls_2253_);
v___x_2284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2281_, v_options_2278_, v___x_2283_);
lean_dec(v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v___y_2261_ = v_a_2275_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2285_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1);
v___x_2286_ = l_Lean_MessageData_ofExpr(v_00_u03c6_2254_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2253_, v___x_2287_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_dec_ref_known(v___x_2288_, 1);
v___y_2261_ = v_a_2275_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_a_2275_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
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
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_a_2275_);
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v_a_2297_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2277_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2277_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_00_u03c6_2254_);
lean_dec(v_cls_2253_);
v_a_2305_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2274_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2274_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed(lean_object* v___f_2345_, lean_object* v_cls_2346_, lean_object* v_00_u03c6_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(v___f_2345_, v_cls_2346_, v_00_u03c6_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(lean_object* v_goal_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___y_2372_; uint8_t v___y_2373_; lean_object* v_cls_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v_val_2378_; lean_object* v___f_2379_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; uint8_t v___x_2406_; 
v_cls_2375_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___x_2376_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(v_cls_2375_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v_val_2378_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_val_2378_);
lean_dec(v_a_2377_);
v___f_2379_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1));
v___x_2406_ = lean_unbox(v_val_2378_);
lean_dec(v_val_2378_);
if (v___x_2406_ == 0)
{
v___y_2381_ = v_a_2363_;
v___y_2382_ = v_a_2364_;
v___y_2383_ = v_a_2365_;
v___y_2384_ = v_a_2366_;
goto v___jp_2380_;
}
else
{
lean_object* v_target_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_target_2407_ = lean_ctor_get(v_goal_2362_, 3);
v___x_2408_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3);
lean_inc_ref(v_target_2407_);
v___x_2409_ = l_Lean_MessageData_ofExpr(v_target_2407_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2375_, v___x_2410_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_dec_ref_known(v___x_2411_, 1);
v___y_2381_ = v_a_2363_;
v___y_2382_ = v_a_2364_;
v___y_2383_ = v_a_2365_;
v___y_2384_ = v_a_2366_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_goal_2362_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
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
v___jp_2368_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
v___jp_2371_:
{
if (v___y_2373_ == 0)
{
lean_dec_ref(v___y_2372_);
goto v___jp_2368_;
}
else
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2372_);
return v___x_2374_;
}
}
v___jp_2380_:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2362_, v___f_2379_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2402_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2402_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2402_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
if (lean_obj_tag(v_a_2386_) == 0)
{
lean_del_object(v___x_2388_);
goto v___jp_2368_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2401_; 
v_val_2390_ = lean_ctor_get(v_a_2386_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2392_ = v_a_2386_;
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_val_2390_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2401_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_snd_2394_; lean_object* v___x_2396_; 
v_snd_2394_ = lean_ctor_get(v_val_2390_, 1);
lean_inc(v_snd_2394_);
lean_dec(v_val_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v_snd_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_snd_2394_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2398_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2396_);
v___x_2398_ = v___x_2388_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
else
{
lean_object* v_a_2403_; uint8_t v___x_2404_; 
v_a_2403_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2404_ = l_Lean_Exception_isInterrupt(v_a_2403_);
if (v___x_2404_ == 0)
{
uint8_t v___x_2405_; 
lean_inc(v_a_2403_);
v___x_2405_ = l_Lean_Exception_isRuntime(v_a_2403_);
v___y_2372_ = v_a_2403_;
v___y_2373_ = v___x_2405_;
goto v___jp_2371_;
}
else
{
v___y_2372_ = v_a_2403_;
v___y_2373_ = v___x_2404_;
goto v___jp_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___boxed(lean_object* v_goal_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(v_goal_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(uint8_t v___y_2427_, lean_object* v_x_2428_){
_start:
{
return v___y_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed(lean_object* v___y_2429_, lean_object* v_x_2430_){
_start:
{
uint8_t v___y_9291__boxed_2431_; uint8_t v_res_2432_; lean_object* v_r_2433_; 
v___y_9291__boxed_2431_ = lean_unbox(v___y_2429_);
v_res_2432_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(v___y_9291__boxed_2431_, v_x_2430_);
lean_dec(v_x_2430_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(lean_object* v_00_u03c6_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_00_u03c6_2446_);
v___x_2453_ = 0;
v___x_2454_ = lean_box(0);
v___x_2455_ = l_Lean_Meta_mkFreshExprMVar(v___x_2452_, v___x_2453_, v___x_2454_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2514_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2514_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2514_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = l_Lean_Expr_mvarId_x21(v_a_2456_);
lean_inc(v___x_2467_);
v___x_2468_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2467_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_dec_ref_known(v___x_2468_, 1);
lean_dec(v___x_2467_);
goto v___jp_2460_;
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2513_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2513_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2513_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
uint8_t v___y_2474_; uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_Exception_isInterrupt(v_a_2469_);
if (v___x_2511_ == 0)
{
uint8_t v___x_2512_; 
lean_inc(v_a_2469_);
v___x_2512_ = l_Lean_Exception_isRuntime(v_a_2469_);
v___y_2474_ = v___x_2512_;
goto v___jp_2473_;
}
else
{
v___y_2474_ = v___x_2511_;
goto v___jp_2473_;
}
v___jp_2473_:
{
if (v___y_2474_ == 0)
{
lean_object* v_ref_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_del_object(v___x_2471_);
lean_dec(v_a_2469_);
v_ref_2475_ = lean_ctor_get(v___y_2449_, 4);
v___x_2476_ = lean_box(v___y_2474_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2477_, 0, v___x_2476_);
v___x_2478_ = l_Lean_SourceInfo_fromRef(v_ref_2475_, v___y_2474_);
v___x_2479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1));
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2));
lean_inc(v___x_2478_);
v___x_2481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2478_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_Lean_Syntax_node1(v___x_2478_, v___x_2479_, v___x_2481_);
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_box(0);
v___x_2485_ = 1;
v___x_2486_ = lean_box(1);
v___x_2487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3));
v___x_2488_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2488_, 0, v___x_2483_);
lean_ctor_set(v___x_2488_, 1, v___x_2484_);
lean_ctor_set(v___x_2488_, 2, v___x_2483_);
lean_ctor_set(v___x_2488_, 3, v___f_2477_);
lean_ctor_set(v___x_2488_, 4, v___x_2486_);
lean_ctor_set(v___x_2488_, 5, v___x_2486_);
lean_ctor_set(v___x_2488_, 6, v___x_2483_);
lean_ctor_set(v___x_2488_, 7, v___x_2487_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8, v___x_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 1, v___x_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 2, v___x_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 3, v___x_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 4, v___y_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 5, v___y_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 6, v___y_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 7, v___y_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 8, v___x_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 9, v___y_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*8 + 10, v___x_2485_);
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4));
v___x_2490_ = l_Lean_Elab_runTactic(v___x_2467_, v___x_2482_, v___x_2488_, v___x_2489_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2499_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_fst_2495_; 
v_fst_2495_ = lean_ctor_get(v_a_2491_, 0);
lean_inc(v_fst_2495_);
lean_dec(v_a_2491_);
if (lean_obj_tag(v_fst_2495_) == 0)
{
lean_del_object(v___x_2493_);
goto v___jp_2460_;
}
else
{
lean_object* v___x_2497_; 
lean_dec(v_fst_2495_);
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2483_);
v___x_2497_ = v___x_2493_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2483_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
v_a_2500_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2490_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2490_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v___x_2509_; 
lean_dec(v___x_2467_);
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
if (v_isShared_2472_ == 0)
{
v___x_2509_ = v___x_2471_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2469_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
v___jp_2460_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v_a_2456_);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2463_);
v___x_2465_ = v___x_2458_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
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
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2455_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2455_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed(lean_object* v_00_u03c6_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(v_00_u03c6_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(lean_object* v_goal_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___f_2540_; lean_object* v___x_2541_; 
v___f_2540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0));
v___x_2541_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2531_, v___f_2540_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2558_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2558_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2558_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
if (lean_obj_tag(v_a_2542_) == 0)
{
lean_del_object(v___x_2544_);
goto v___jp_2537_;
}
else
{
lean_object* v_val_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2557_; 
v_val_2546_ = lean_ctor_get(v_a_2542_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_a_2542_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2548_ = v_a_2542_;
v_isShared_2549_ = v_isSharedCheck_2557_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_val_2546_);
lean_dec(v_a_2542_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2557_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_snd_2550_; lean_object* v___x_2552_; 
v_snd_2550_ = lean_ctor_get(v_val_2546_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_val_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_snd_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_snd_2550_);
v___x_2552_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2552_);
v___x_2554_ = v___x_2544_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2570_; 
v_a_2559_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2561_ = v___x_2541_;
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2541_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
uint8_t v___y_2564_; uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Exception_isInterrupt(v_a_2559_);
if (v___x_2568_ == 0)
{
uint8_t v___x_2569_; 
lean_inc(v_a_2559_);
v___x_2569_ = l_Lean_Exception_isRuntime(v_a_2559_);
v___y_2564_ = v___x_2569_;
goto v___jp_2563_;
}
else
{
v___y_2564_ = v___x_2568_;
goto v___jp_2563_;
}
v___jp_2563_:
{
if (v___y_2564_ == 0)
{
lean_del_object(v___x_2561_);
lean_dec(v_a_2559_);
goto v___jp_2537_;
}
else
{
lean_object* v___x_2566_; 
if (v_isShared_2562_ == 0)
{
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2559_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
v___jp_2537_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___boxed(lean_object* v_goal_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(v_goal_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2577_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rfl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
}
#ifdef __cplusplus
}
#endif
