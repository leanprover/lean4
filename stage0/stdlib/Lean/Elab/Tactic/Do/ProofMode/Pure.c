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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed, .m_arity = 8, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_MVarId_applyRflAndAndIntro___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value)} };
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(lean_object* v___y_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(v___y_1_, v___y_2_, v___y_3_, v___y_4_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed(lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(v___y_9_, v___y_10_, v___y_11_, v___y_12_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
return v_res_14_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(lean_object* v_name_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_15_, v___y_18_, v___y_19_);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_15_ = stack[0].m_obj;
lean_object* v___y_16_ = stack[1].m_obj;
lean_object* v___y_17_ = stack[2].m_obj;
lean_object* v___y_18_ = stack[3].m_obj;
lean_object* v___y_19_ = stack[4].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(v_name_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed(lean_object* v_name_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(v_name_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2(lean_object* v_fst_32_, lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v___x_36_, lean_object* v___x_37_, lean_object* v_00_u03c3s_38_, lean_object* v_hyp_39_, lean_object* v_00_u03c6_40_, lean_object* v_inst_41_, lean_object* v_u_42_, lean_object* v_fst_43_, lean_object* v_toPure_44_, lean_object* v_prf_45_){
_start:
{
lean_object* v_u_46_; lean_object* v_00_u03c3s_47_; lean_object* v_hyps_48_; lean_object* v_target_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_65_; 
v_u_46_ = lean_ctor_get(v_fst_32_, 0);
v_00_u03c3s_47_ = lean_ctor_get(v_fst_32_, 1);
v_hyps_48_ = lean_ctor_get(v_fst_32_, 2);
v_target_49_ = lean_ctor_get(v_fst_32_, 3);
v_isSharedCheck_65_ = !lean_is_exclusive(v_fst_32_);
if (v_isSharedCheck_65_ == 0)
{
v___x_51_ = v_fst_32_;
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_target_49_);
lean_inc(v_hyps_48_);
lean_inc(v_00_u03c3s_47_);
lean_inc(v_u_46_);
lean_dec(v_fst_32_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_65_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_prf_57_; lean_object* v___x_58_; lean_object* v_goal_60_; 
v___x_53_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_54_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1));
v___x_55_ = l_Lean_Name_mkStr6(v___x_33_, v___x_34_, v___x_35_, v___x_36_, v___x_53_, v___x_54_);
v___x_56_ = l_Lean_mkConst(v___x_55_, v___x_37_);
lean_inc_ref(v_target_49_);
lean_inc_ref(v_hyp_39_);
lean_inc_ref(v_hyps_48_);
lean_inc_ref(v_00_u03c3s_38_);
v_prf_57_ = l_Lean_mkApp7(v___x_56_, v_00_u03c3s_38_, v_hyps_48_, v_hyp_39_, v_target_49_, v_00_u03c6_40_, v_inst_41_, v_prf_45_);
v___x_58_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_42_, v_00_u03c3s_38_, v_hyps_48_, v_hyp_39_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 2, v___x_58_);
v_goal_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_u_46_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_00_u03c3s_47_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_target_49_);
v_goal_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_goal_60_);
lean_ctor_set(v___x_61_, 1, v_prf_57_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_fst_43_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_apply_2(v_toPure_44_, lean_box(0), v___x_62_);
return v___x_63_;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(lean_object* v___x_66_, lean_object* v___x_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v_00_u03c3s_71_, lean_object* v_hyp_72_, lean_object* v_00_u03c6_73_, lean_object* v_inst_74_, lean_object* v_u_75_, lean_object* v_toPure_76_, lean_object* v_h_77_, uint8_t v___x_78_, lean_object* v_inst_79_, lean_object* v_toBind_80_, lean_object* v_____x_81_){
_start:
{
lean_object* v_snd_82_; lean_object* v_fst_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___f_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_snd_82_ = lean_ctor_get(v_____x_81_, 1);
lean_inc(v_snd_82_);
v_fst_83_ = lean_ctor_get(v_____x_81_, 0);
lean_inc(v_fst_83_);
lean_dec_ref(v_____x_81_);
v_fst_84_ = lean_ctor_get(v_snd_82_, 0);
lean_inc(v_fst_84_);
v_snd_85_ = lean_ctor_get(v_snd_82_, 1);
lean_inc(v_snd_85_);
lean_dec(v_snd_82_);
v___f_86_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2), 14, 13);
lean_closure_set(v___f_86_, 0, v_fst_84_);
lean_closure_set(v___f_86_, 1, v___x_66_);
lean_closure_set(v___f_86_, 2, v___x_67_);
lean_closure_set(v___f_86_, 3, v___x_68_);
lean_closure_set(v___f_86_, 4, v___x_69_);
lean_closure_set(v___f_86_, 5, v___x_70_);
lean_closure_set(v___f_86_, 6, v_00_u03c3s_71_);
lean_closure_set(v___f_86_, 7, v_hyp_72_);
lean_closure_set(v___f_86_, 8, v_00_u03c6_73_);
lean_closure_set(v___f_86_, 9, v_inst_74_);
lean_closure_set(v___f_86_, 10, v_u_75_);
lean_closure_set(v___f_86_, 11, v_fst_83_);
lean_closure_set(v___f_86_, 12, v_toPure_76_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_array_push(v___x_88_, v_h_77_);
v___x_90_ = 1;
v___x_91_ = 1;
v___x_92_ = lean_box(v___x_78_);
v___x_93_ = lean_box(v___x_90_);
v___x_94_ = lean_box(v___x_78_);
v___x_95_ = lean_box(v___x_90_);
v___x_96_ = lean_box(v___x_91_);
v___x_97_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_97_, 0, v___x_89_);
lean_closure_set(v___x_97_, 1, v_snd_85_);
lean_closure_set(v___x_97_, 2, v___x_92_);
lean_closure_set(v___x_97_, 3, v___x_93_);
lean_closure_set(v___x_97_, 4, v___x_94_);
lean_closure_set(v___x_97_, 5, v___x_95_);
lean_closure_set(v___x_97_, 6, v___x_96_);
v___x_98_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_97_);
v___x_99_ = lean_apply_4(v_toBind_80_, lean_box(0), lean_box(0), v___x_98_, v___f_86_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_66_ = stack[0].m_obj;
lean_object* v___x_67_ = stack[1].m_obj;
lean_object* v___x_68_ = stack[2].m_obj;
lean_object* v___x_69_ = stack[3].m_obj;
lean_object* v___x_70_ = stack[4].m_obj;
lean_object* v_00_u03c3s_71_ = stack[5].m_obj;
lean_object* v_hyp_72_ = stack[6].m_obj;
lean_object* v_00_u03c6_73_ = stack[7].m_obj;
lean_object* v_inst_74_ = stack[8].m_obj;
lean_object* v_u_75_ = stack[9].m_obj;
lean_object* v_toPure_76_ = stack[10].m_obj;
lean_object* v_h_77_ = stack[11].m_obj;
uint8_t v___x_78_ = stack[12].m_num;
lean_object* v_inst_79_ = stack[13].m_obj;
lean_object* v_toBind_80_ = stack[14].m_obj;
lean_object* v_____x_81_ = stack[15].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(v___x_66_, v___x_67_, v___x_68_, v___x_69_, v___x_70_, v_00_u03c3s_71_, v_hyp_72_, v_00_u03c6_73_, v_inst_74_, v_u_75_, v_toPure_76_, v_h_77_, v___x_78_, v_inst_79_, v_toBind_80_, v_____x_81_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed(lean_object* v___x_101_, lean_object* v___x_102_, lean_object* v___x_103_, lean_object* v___x_104_, lean_object* v___x_105_, lean_object* v_00_u03c3s_106_, lean_object* v_hyp_107_, lean_object* v_00_u03c6_108_, lean_object* v_inst_109_, lean_object* v_u_110_, lean_object* v_toPure_111_, lean_object* v_h_112_, lean_object* v___x_113_, lean_object* v_inst_114_, lean_object* v_toBind_115_, lean_object* v_____x_116_){
_start:
{
uint8_t v___x_532__boxed_117_; lean_object* v_res_118_; 
v___x_532__boxed_117_ = lean_unbox(v___x_113_);
v_res_118_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(v___x_101_, v___x_102_, v___x_103_, v___x_104_, v___x_105_, v_00_u03c3s_106_, v_hyp_107_, v_00_u03c6_108_, v_inst_109_, v_u_110_, v_toPure_111_, v_h_112_, v___x_532__boxed_117_, v_inst_114_, v_toBind_115_, v_____x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4(lean_object* v_k_119_, lean_object* v_00_u03c6_120_, lean_object* v_h_121_, lean_object* v_toBind_122_, lean_object* v___f_123_, lean_object* v_____r_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_apply_2(v_k_119_, v_00_u03c6_120_, v_h_121_);
v___x_126_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_125_, v___f_123_);
return v___x_126_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(lean_object* v_00_u03c6_127_, lean_object* v___x_128_, lean_object* v___x_129_, lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v___x_132_, lean_object* v_00_u03c3s_133_, lean_object* v_hyp_134_, lean_object* v_inst_135_, lean_object* v_u_136_, lean_object* v_toPure_137_, lean_object* v_h_138_, lean_object* v_inst_139_, lean_object* v_toBind_140_, lean_object* v_k_141_, lean_object* v_snd_142_, lean_object* v_____do__lift_143_){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc_ref_n(v_00_u03c6_127_, 2);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_00_u03c6_127_);
v___x_145_ = 0;
v___x_146_ = lean_box(v___x_145_);
lean_inc_n(v_toBind_140_, 2);
lean_inc(v_inst_139_);
lean_inc_ref_n(v_h_138_, 2);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_147_, 0, v___x_128_);
lean_closure_set(v___f_147_, 1, v___x_129_);
lean_closure_set(v___f_147_, 2, v___x_130_);
lean_closure_set(v___f_147_, 3, v___x_131_);
lean_closure_set(v___f_147_, 4, v___x_132_);
lean_closure_set(v___f_147_, 5, v_00_u03c3s_133_);
lean_closure_set(v___f_147_, 6, v_hyp_134_);
lean_closure_set(v___f_147_, 7, v_00_u03c6_127_);
lean_closure_set(v___f_147_, 8, v_inst_135_);
lean_closure_set(v___f_147_, 9, v_u_136_);
lean_closure_set(v___f_147_, 10, v_toPure_137_);
lean_closure_set(v___f_147_, 11, v_h_138_);
lean_closure_set(v___f_147_, 12, v___x_146_);
lean_closure_set(v___f_147_, 13, v_inst_139_);
lean_closure_set(v___f_147_, 14, v_toBind_140_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4), 6, 5);
lean_closure_set(v___f_148_, 0, v_k_141_);
lean_closure_set(v___f_148_, 1, v_00_u03c6_127_);
lean_closure_set(v___f_148_, 2, v_h_138_);
lean_closure_set(v___f_148_, 3, v_toBind_140_);
lean_closure_set(v___f_148_, 4, v___f_147_);
v___x_149_ = lean_box(v___x_145_);
v___x_150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed), 10, 5);
lean_closure_set(v___x_150_, 0, v_snd_142_);
lean_closure_set(v___x_150_, 1, v_____do__lift_143_);
lean_closure_set(v___x_150_, 2, v_h_138_);
lean_closure_set(v___x_150_, 3, v___x_144_);
lean_closure_set(v___x_150_, 4, v___x_149_);
v___x_151_ = lean_apply_2(v_inst_139_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_toBind_140_, lean_box(0), lean_box(0), v___x_151_, v___f_148_);
return v___x_152_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c6_127_ = stack[0].m_obj;
lean_object* v___x_128_ = stack[1].m_obj;
lean_object* v___x_129_ = stack[2].m_obj;
lean_object* v___x_130_ = stack[3].m_obj;
lean_object* v___x_131_ = stack[4].m_obj;
lean_object* v___x_132_ = stack[5].m_obj;
lean_object* v_00_u03c3s_133_ = stack[6].m_obj;
lean_object* v_hyp_134_ = stack[7].m_obj;
lean_object* v_inst_135_ = stack[8].m_obj;
lean_object* v_u_136_ = stack[9].m_obj;
lean_object* v_toPure_137_ = stack[10].m_obj;
lean_object* v_h_138_ = stack[11].m_obj;
lean_object* v_inst_139_ = stack[12].m_obj;
lean_object* v_toBind_140_ = stack[13].m_obj;
lean_object* v_k_141_ = stack[14].m_obj;
lean_object* v_snd_142_ = stack[15].m_obj;
lean_object* v_____do__lift_143_ = stack[16].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(v_00_u03c6_127_, v___x_128_, v___x_129_, v___x_130_, v___x_131_, v___x_132_, v_00_u03c3s_133_, v_hyp_134_, v_inst_135_, v_u_136_, v_toPure_137_, v_h_138_, v_inst_139_, v_toBind_140_, v_k_141_, v_snd_142_, v_____do__lift_143_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_00_u03c6_154_ = _args[0];
lean_object* v___x_155_ = _args[1];
lean_object* v___x_156_ = _args[2];
lean_object* v___x_157_ = _args[3];
lean_object* v___x_158_ = _args[4];
lean_object* v___x_159_ = _args[5];
lean_object* v_00_u03c3s_160_ = _args[6];
lean_object* v_hyp_161_ = _args[7];
lean_object* v_inst_162_ = _args[8];
lean_object* v_u_163_ = _args[9];
lean_object* v_toPure_164_ = _args[10];
lean_object* v_h_165_ = _args[11];
lean_object* v_inst_166_ = _args[12];
lean_object* v_toBind_167_ = _args[13];
lean_object* v_k_168_ = _args[14];
lean_object* v_snd_169_ = _args[15];
lean_object* v_____do__lift_170_ = _args[16];
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(v_00_u03c6_154_, v___x_155_, v___x_156_, v___x_157_, v___x_158_, v___x_159_, v_00_u03c3s_160_, v_hyp_161_, v_inst_162_, v_u_163_, v_toPure_164_, v_h_165_, v_inst_166_, v_toBind_167_, v_k_168_, v_snd_169_, v_____do__lift_170_);
return v_res_171_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(lean_object* v_00_u03c6_172_, lean_object* v___x_173_, lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v_00_u03c3s_178_, lean_object* v_hyp_179_, lean_object* v_inst_180_, lean_object* v_u_181_, lean_object* v_toPure_182_, lean_object* v_inst_183_, lean_object* v_toBind_184_, lean_object* v_k_185_, lean_object* v_snd_186_, lean_object* v___f_187_, lean_object* v_h_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc(v_toBind_184_);
lean_inc(v_inst_183_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_189_, 0, v_00_u03c6_172_);
lean_closure_set(v___f_189_, 1, v___x_173_);
lean_closure_set(v___f_189_, 2, v___x_174_);
lean_closure_set(v___f_189_, 3, v___x_175_);
lean_closure_set(v___f_189_, 4, v___x_176_);
lean_closure_set(v___f_189_, 5, v___x_177_);
lean_closure_set(v___f_189_, 6, v_00_u03c3s_178_);
lean_closure_set(v___f_189_, 7, v_hyp_179_);
lean_closure_set(v___f_189_, 8, v_inst_180_);
lean_closure_set(v___f_189_, 9, v_u_181_);
lean_closure_set(v___f_189_, 10, v_toPure_182_);
lean_closure_set(v___f_189_, 11, v_h_188_);
lean_closure_set(v___f_189_, 12, v_inst_183_);
lean_closure_set(v___f_189_, 13, v_toBind_184_);
lean_closure_set(v___f_189_, 14, v_k_185_);
lean_closure_set(v___f_189_, 15, v_snd_186_);
v___x_190_ = lean_apply_2(v_inst_183_, lean_box(0), v___f_187_);
v___x_191_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_190_, v___f_189_);
return v___x_191_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c6_172_ = stack[0].m_obj;
lean_object* v___x_173_ = stack[1].m_obj;
lean_object* v___x_174_ = stack[2].m_obj;
lean_object* v___x_175_ = stack[3].m_obj;
lean_object* v___x_176_ = stack[4].m_obj;
lean_object* v___x_177_ = stack[5].m_obj;
lean_object* v_00_u03c3s_178_ = stack[6].m_obj;
lean_object* v_hyp_179_ = stack[7].m_obj;
lean_object* v_inst_180_ = stack[8].m_obj;
lean_object* v_u_181_ = stack[9].m_obj;
lean_object* v_toPure_182_ = stack[10].m_obj;
lean_object* v_inst_183_ = stack[11].m_obj;
lean_object* v_toBind_184_ = stack[12].m_obj;
lean_object* v_k_185_ = stack[13].m_obj;
lean_object* v_snd_186_ = stack[14].m_obj;
lean_object* v___f_187_ = stack[15].m_obj;
lean_object* v_h_188_ = stack[16].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(v_00_u03c6_172_, v___x_173_, v___x_174_, v___x_175_, v___x_176_, v___x_177_, v_00_u03c3s_178_, v_hyp_179_, v_inst_180_, v_u_181_, v_toPure_182_, v_inst_183_, v_toBind_184_, v_k_185_, v_snd_186_, v___f_187_, v_h_188_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_00_u03c6_193_ = _args[0];
lean_object* v___x_194_ = _args[1];
lean_object* v___x_195_ = _args[2];
lean_object* v___x_196_ = _args[3];
lean_object* v___x_197_ = _args[4];
lean_object* v___x_198_ = _args[5];
lean_object* v_00_u03c3s_199_ = _args[6];
lean_object* v_hyp_200_ = _args[7];
lean_object* v_inst_201_ = _args[8];
lean_object* v_u_202_ = _args[9];
lean_object* v_toPure_203_ = _args[10];
lean_object* v_inst_204_ = _args[11];
lean_object* v_toBind_205_ = _args[12];
lean_object* v_k_206_ = _args[13];
lean_object* v_snd_207_ = _args[14];
lean_object* v___f_208_ = _args[15];
lean_object* v_h_209_ = _args[16];
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(v_00_u03c6_193_, v___x_194_, v___x_195_, v___x_196_, v___x_197_, v___x_198_, v_00_u03c3s_199_, v_hyp_200_, v_inst_201_, v_u_202_, v_toPure_203_, v_inst_204_, v_toBind_205_, v_k_206_, v_snd_207_, v___f_208_, v_h_209_);
return v_res_210_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(lean_object* v_00_u03c6_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v___x_216_, lean_object* v_00_u03c3s_217_, lean_object* v_hyp_218_, lean_object* v_inst_219_, lean_object* v_u_220_, lean_object* v_toPure_221_, lean_object* v_inst_222_, lean_object* v_toBind_223_, lean_object* v_k_224_, lean_object* v___f_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_____x_228_){
_start:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___f_231_; lean_object* v___x_232_; 
v_fst_229_ = lean_ctor_get(v_____x_228_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v_____x_228_, 1);
lean_inc(v_snd_230_);
lean_dec_ref(v_____x_228_);
lean_inc_ref(v_00_u03c6_211_);
v___f_231_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_231_, 0, v_00_u03c6_211_);
lean_closure_set(v___f_231_, 1, v___x_212_);
lean_closure_set(v___f_231_, 2, v___x_213_);
lean_closure_set(v___f_231_, 3, v___x_214_);
lean_closure_set(v___f_231_, 4, v___x_215_);
lean_closure_set(v___f_231_, 5, v___x_216_);
lean_closure_set(v___f_231_, 6, v_00_u03c3s_217_);
lean_closure_set(v___f_231_, 7, v_hyp_218_);
lean_closure_set(v___f_231_, 8, v_inst_219_);
lean_closure_set(v___f_231_, 9, v_u_220_);
lean_closure_set(v___f_231_, 10, v_toPure_221_);
lean_closure_set(v___f_231_, 11, v_inst_222_);
lean_closure_set(v___f_231_, 12, v_toBind_223_);
lean_closure_set(v___f_231_, 13, v_k_224_);
lean_closure_set(v___f_231_, 14, v_snd_230_);
lean_closure_set(v___f_231_, 15, v___f_225_);
v___x_232_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_226_, v_inst_227_, v_fst_229_, v_00_u03c6_211_, v___f_231_);
return v___x_232_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c6_211_ = stack[0].m_obj;
lean_object* v___x_212_ = stack[1].m_obj;
lean_object* v___x_213_ = stack[2].m_obj;
lean_object* v___x_214_ = stack[3].m_obj;
lean_object* v___x_215_ = stack[4].m_obj;
lean_object* v___x_216_ = stack[5].m_obj;
lean_object* v_00_u03c3s_217_ = stack[6].m_obj;
lean_object* v_hyp_218_ = stack[7].m_obj;
lean_object* v_inst_219_ = stack[8].m_obj;
lean_object* v_u_220_ = stack[9].m_obj;
lean_object* v_toPure_221_ = stack[10].m_obj;
lean_object* v_inst_222_ = stack[11].m_obj;
lean_object* v_toBind_223_ = stack[12].m_obj;
lean_object* v_k_224_ = stack[13].m_obj;
lean_object* v___f_225_ = stack[14].m_obj;
lean_object* v_inst_226_ = stack[15].m_obj;
lean_object* v_inst_227_ = stack[16].m_obj;
lean_object* v_____x_228_ = stack[17].m_obj;
lean_object* v_res_233_;
v_res_233_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(v_00_u03c6_211_, v___x_212_, v___x_213_, v___x_214_, v___x_215_, v___x_216_, v_00_u03c3s_217_, v_hyp_218_, v_inst_219_, v_u_220_, v_toPure_221_, v_inst_222_, v_toBind_223_, v_k_224_, v___f_225_, v_inst_226_, v_inst_227_, v_____x_228_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_00_u03c6_234_ = _args[0];
lean_object* v___x_235_ = _args[1];
lean_object* v___x_236_ = _args[2];
lean_object* v___x_237_ = _args[3];
lean_object* v___x_238_ = _args[4];
lean_object* v___x_239_ = _args[5];
lean_object* v_00_u03c3s_240_ = _args[6];
lean_object* v_hyp_241_ = _args[7];
lean_object* v_inst_242_ = _args[8];
lean_object* v_u_243_ = _args[9];
lean_object* v_toPure_244_ = _args[10];
lean_object* v_inst_245_ = _args[11];
lean_object* v_toBind_246_ = _args[12];
lean_object* v_k_247_ = _args[13];
lean_object* v___f_248_ = _args[14];
lean_object* v_inst_249_ = _args[15];
lean_object* v_inst_250_ = _args[16];
lean_object* v_____x_251_ = _args[17];
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(v_00_u03c6_234_, v___x_235_, v___x_236_, v___x_237_, v___x_238_, v___x_239_, v_00_u03c3s_240_, v_hyp_241_, v_inst_242_, v_u_243_, v_toPure_244_, v_inst_245_, v_toBind_246_, v_k_247_, v___f_248_, v_inst_249_, v_inst_250_, v_____x_251_);
return v_res_252_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(lean_object* v_00_u03c6_253_, lean_object* v___x_254_, lean_object* v___x_255_, lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v___x_258_, lean_object* v_00_u03c3s_259_, lean_object* v_hyp_260_, lean_object* v_u_261_, lean_object* v_toPure_262_, lean_object* v_inst_263_, lean_object* v_toBind_264_, lean_object* v_k_265_, lean_object* v___f_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v___f_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_inc(v_toBind_264_);
lean_inc(v_inst_263_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_271_, 0, v_00_u03c6_253_);
lean_closure_set(v___f_271_, 1, v___x_254_);
lean_closure_set(v___f_271_, 2, v___x_255_);
lean_closure_set(v___f_271_, 3, v___x_256_);
lean_closure_set(v___f_271_, 4, v___x_257_);
lean_closure_set(v___f_271_, 5, v___x_258_);
lean_closure_set(v___f_271_, 6, v_00_u03c3s_259_);
lean_closure_set(v___f_271_, 7, v_hyp_260_);
lean_closure_set(v___f_271_, 8, v_inst_270_);
lean_closure_set(v___f_271_, 9, v_u_261_);
lean_closure_set(v___f_271_, 10, v_toPure_262_);
lean_closure_set(v___f_271_, 11, v_inst_263_);
lean_closure_set(v___f_271_, 12, v_toBind_264_);
lean_closure_set(v___f_271_, 13, v_k_265_);
lean_closure_set(v___f_271_, 14, v___f_266_);
lean_closure_set(v___f_271_, 15, v_inst_267_);
lean_closure_set(v___f_271_, 16, v_inst_268_);
v___x_272_ = lean_apply_2(v_inst_263_, lean_box(0), v___f_269_);
v___x_273_ = lean_apply_4(v_toBind_264_, lean_box(0), lean_box(0), v___x_272_, v___f_271_);
return v___x_273_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c6_253_ = stack[0].m_obj;
lean_object* v___x_254_ = stack[1].m_obj;
lean_object* v___x_255_ = stack[2].m_obj;
lean_object* v___x_256_ = stack[3].m_obj;
lean_object* v___x_257_ = stack[4].m_obj;
lean_object* v___x_258_ = stack[5].m_obj;
lean_object* v_00_u03c3s_259_ = stack[6].m_obj;
lean_object* v_hyp_260_ = stack[7].m_obj;
lean_object* v_u_261_ = stack[8].m_obj;
lean_object* v_toPure_262_ = stack[9].m_obj;
lean_object* v_inst_263_ = stack[10].m_obj;
lean_object* v_toBind_264_ = stack[11].m_obj;
lean_object* v_k_265_ = stack[12].m_obj;
lean_object* v___f_266_ = stack[13].m_obj;
lean_object* v_inst_267_ = stack[14].m_obj;
lean_object* v_inst_268_ = stack[15].m_obj;
lean_object* v___f_269_ = stack[16].m_obj;
lean_object* v_inst_270_ = stack[17].m_obj;
lean_object* v_res_274_;
v_res_274_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(v_00_u03c6_253_, v___x_254_, v___x_255_, v___x_256_, v___x_257_, v___x_258_, v_00_u03c3s_259_, v_hyp_260_, v_u_261_, v_toPure_262_, v_inst_263_, v_toBind_264_, v_k_265_, v___f_266_, v_inst_267_, v_inst_268_, v___f_269_, v_inst_270_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_00_u03c6_275_ = _args[0];
lean_object* v___x_276_ = _args[1];
lean_object* v___x_277_ = _args[2];
lean_object* v___x_278_ = _args[3];
lean_object* v___x_279_ = _args[4];
lean_object* v___x_280_ = _args[5];
lean_object* v_00_u03c3s_281_ = _args[6];
lean_object* v_hyp_282_ = _args[7];
lean_object* v_u_283_ = _args[8];
lean_object* v_toPure_284_ = _args[9];
lean_object* v_inst_285_ = _args[10];
lean_object* v_toBind_286_ = _args[11];
lean_object* v_k_287_ = _args[12];
lean_object* v___f_288_ = _args[13];
lean_object* v_inst_289_ = _args[14];
lean_object* v_inst_290_ = _args[15];
lean_object* v___f_291_ = _args[16];
lean_object* v_inst_292_ = _args[17];
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(v_00_u03c6_275_, v___x_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, v_00_u03c3s_281_, v_hyp_282_, v_u_283_, v_toPure_284_, v_inst_285_, v_toBind_286_, v_k_287_, v___f_288_, v_inst_289_, v_inst_290_, v___f_291_, v_inst_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9(lean_object* v_u_305_, lean_object* v_00_u03c3s_306_, lean_object* v_hyp_307_, lean_object* v_toPure_308_, lean_object* v_inst_309_, lean_object* v_toBind_310_, lean_object* v_k_311_, lean_object* v___f_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v___f_315_, lean_object* v_00_u03c6_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_318_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_320_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_322_ = lean_box(0);
lean_inc(v_u_305_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v_u_305_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v_toBind_310_);
lean_inc(v_inst_309_);
lean_inc_ref(v_hyp_307_);
lean_inc_ref(v_00_u03c3s_306_);
lean_inc_ref(v___x_323_);
lean_inc_ref(v_00_u03c6_316_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed), 18, 17);
lean_closure_set(v___f_324_, 0, v_00_u03c6_316_);
lean_closure_set(v___f_324_, 1, v___x_317_);
lean_closure_set(v___f_324_, 2, v___x_318_);
lean_closure_set(v___f_324_, 3, v___x_319_);
lean_closure_set(v___f_324_, 4, v___x_320_);
lean_closure_set(v___f_324_, 5, v___x_323_);
lean_closure_set(v___f_324_, 6, v_00_u03c3s_306_);
lean_closure_set(v___f_324_, 7, v_hyp_307_);
lean_closure_set(v___f_324_, 8, v_u_305_);
lean_closure_set(v___f_324_, 9, v_toPure_308_);
lean_closure_set(v___f_324_, 10, v_inst_309_);
lean_closure_set(v___f_324_, 11, v_toBind_310_);
lean_closure_set(v___f_324_, 12, v_k_311_);
lean_closure_set(v___f_324_, 13, v___f_312_);
lean_closure_set(v___f_324_, 14, v_inst_313_);
lean_closure_set(v___f_324_, 15, v_inst_314_);
lean_closure_set(v___f_324_, 16, v___f_315_);
v___x_325_ = l_Lean_mkConst(v___x_321_, v___x_323_);
v___x_326_ = l_Lean_mkApp3(v___x_325_, v_00_u03c3s_306_, v_hyp_307_, v_00_u03c6_316_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance___boxed), 7, 2);
lean_closure_set(v___x_328_, 0, v___x_326_);
lean_closure_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_apply_2(v_inst_309_, lean_box(0), v___x_328_);
v___x_330_ = lean_apply_4(v_toBind_310_, lean_box(0), lean_box(0), v___x_329_, v___f_324_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_box(0);
v___x_332_ = l_Lean_mkSort(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2(void){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = lean_box(0);
v___x_336_ = 0;
v___x_337_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_338_ = lean_box(v___x_336_);
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_339_, 0, v___x_337_);
lean_closure_set(v___x_339_, 1, v___x_338_);
lean_closure_set(v___x_339_, 2, v___x_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10(lean_object* v_00_u03c3s_340_, lean_object* v_hyp_341_, lean_object* v_toPure_342_, lean_object* v_inst_343_, lean_object* v_toBind_344_, lean_object* v_k_345_, lean_object* v___f_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v___f_349_, lean_object* v_u_350_){
_start:
{
lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_inc(v_toBind_344_);
lean_inc(v_inst_343_);
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9), 12, 11);
lean_closure_set(v___f_351_, 0, v_u_350_);
lean_closure_set(v___f_351_, 1, v_00_u03c3s_340_);
lean_closure_set(v___f_351_, 2, v_hyp_341_);
lean_closure_set(v___f_351_, 3, v_toPure_342_);
lean_closure_set(v___f_351_, 4, v_inst_343_);
lean_closure_set(v___f_351_, 5, v_toBind_344_);
lean_closure_set(v___f_351_, 6, v_k_345_);
lean_closure_set(v___f_351_, 7, v___f_346_);
lean_closure_set(v___f_351_, 8, v_inst_347_);
lean_closure_set(v___f_351_, 9, v_inst_348_);
lean_closure_set(v___f_351_, 10, v___f_349_);
v___x_352_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2);
v___x_353_ = lean_apply_2(v_inst_343_, lean_box(0), v___x_352_);
v___x_354_ = lean_apply_4(v_toBind_344_, lean_box(0), lean_box(0), v___x_353_, v___f_351_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_00_u03c3s_360_, lean_object* v_hyp_361_, lean_object* v_name_362_, lean_object* v_k_363_){
_start:
{
lean_object* v_toApplicative_364_; lean_object* v_toBind_365_; lean_object* v_toPure_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
v_toApplicative_364_ = lean_ctor_get(v_inst_357_, 0);
v_toBind_365_ = lean_ctor_get(v_inst_357_, 1);
lean_inc_n(v_toBind_365_, 2);
v_toPure_366_ = lean_ctor_get(v_toApplicative_364_, 1);
lean_inc(v_toPure_366_);
v___f_367_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0));
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_368_, 0, v_name_362_);
v___x_369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1));
lean_inc(v_inst_359_);
v___x_370_ = lean_apply_2(v_inst_359_, lean_box(0), v___x_369_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10), 11, 10);
lean_closure_set(v___f_371_, 0, v_00_u03c3s_360_);
lean_closure_set(v___f_371_, 1, v_hyp_361_);
lean_closure_set(v___f_371_, 2, v_toPure_366_);
lean_closure_set(v___f_371_, 3, v_inst_359_);
lean_closure_set(v___f_371_, 4, v_toBind_365_);
lean_closure_set(v___f_371_, 5, v_k_363_);
lean_closure_set(v___f_371_, 6, v___f_367_);
lean_closure_set(v___f_371_, 7, v_inst_358_);
lean_closure_set(v___f_371_, 8, v_inst_357_);
lean_closure_set(v___f_371_, 9, v___f_368_);
v___x_372_ = lean_apply_4(v_toBind_365_, lean_box(0), lean_box(0), v___x_370_, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore(lean_object* v_m_373_, lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_00_u03c3s_378_, lean_object* v_hyp_379_, lean_object* v_name_380_, lean_object* v_k_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(v_inst_375_, v_inst_376_, v_inst_377_, v_00_u03c3s_378_, v_hyp_379_, v_name_380_, v_k_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_box(0);
v___x_384_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
return v___x_385_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_389_;
v_res_389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___boxed(lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v_res_391_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(lean_object* v_00_u03b1_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_402_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_393_ = stack[1].m_obj;
lean_object* v___y_394_ = stack[2].m_obj;
lean_object* v___y_395_ = stack[3].m_obj;
lean_object* v___y_396_ = stack[4].m_obj;
lean_object* v___y_397_ = stack[5].m_obj;
lean_object* v___y_398_ = stack[6].m_obj;
lean_object* v___y_399_ = stack[7].m_obj;
lean_object* v___y_400_ = stack[8].m_obj;
lean_object* v_res_403_;
v_res_403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(lean_box(0), v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___boxed(lean_object* v_00_u03b1_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(v_00_u03b1_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_414_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(lean_object* v_x_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
v___x_425_ = lean_apply_9(v_x_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
return v___x_425_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_415_ = stack[0].m_obj;
lean_object* v___y_416_ = stack[1].m_obj;
lean_object* v___y_417_ = stack[2].m_obj;
lean_object* v___y_418_ = stack[3].m_obj;
lean_object* v___y_419_ = stack[4].m_obj;
lean_object* v___y_420_ = stack[5].m_obj;
lean_object* v___y_421_ = stack[6].m_obj;
lean_object* v___y_422_ = stack[7].m_obj;
lean_object* v___y_423_ = stack[8].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(v_x_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed(lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(v_x_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_437_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(lean_object* v_mvarId_438_, lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___f_449_; lean_object* v___x_450_; 
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_449_, 0, v_x_439_);
lean_closure_set(v___f_449_, 1, v___y_440_);
lean_closure_set(v___f_449_, 2, v___y_441_);
lean_closure_set(v___f_449_, 3, v___y_442_);
lean_closure_set(v___f_449_, 4, v___y_443_);
v___x_450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_438_, v___f_449_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_438_ = stack[0].m_obj;
lean_object* v_x_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v___y_445_ = stack[7].m_obj;
lean_object* v___y_446_ = stack[8].m_obj;
lean_object* v___y_447_ = stack[9].m_obj;
lean_object* v_res_459_;
v_res_459_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_mvarId_438_, v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___boxed(lean_object* v_mvarId_460_, lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_mvarId_460_, v_x_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_471_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(lean_object* v_00_u03b1_472_, lean_object* v_mvarId_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_mvarId_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_473_ = stack[1].m_obj;
lean_object* v_x_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v___y_479_ = stack[7].m_obj;
lean_object* v___y_480_ = stack[8].m_obj;
lean_object* v___y_481_ = stack[9].m_obj;
lean_object* v___y_482_ = stack[10].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(lean_box(0), v_mvarId_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___boxed(lean_object* v_00_u03b1_486_, lean_object* v_mvarId_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(v_00_u03b1_486_, v_mvarId_487_, v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_498_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(lean_object* v_a_499_, lean_object* v_snd_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_512_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_a_499_, v_snd_500_);
lean_inc_ref(v___x_512_);
v___x_513_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_512_);
v___x_514_ = lean_box(0);
v___x_515_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_513_, v___x_514_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_inc(v_a_516_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_512_);
lean_ctor_set(v___x_520_, 1, v_a_516_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_a_516_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v___x_512_);
v_a_526_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_515_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_515_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_499_ = stack[0].m_obj;
lean_object* v_snd_500_ = stack[1].m_obj;
lean_object* v_x_501_ = stack[2].m_obj;
lean_object* v_x_502_ = stack[3].m_obj;
lean_object* v___y_503_ = stack[4].m_obj;
lean_object* v___y_504_ = stack[5].m_obj;
lean_object* v___y_505_ = stack[6].m_obj;
lean_object* v___y_506_ = stack[7].m_obj;
lean_object* v___y_507_ = stack[8].m_obj;
lean_object* v___y_508_ = stack[9].m_obj;
lean_object* v___y_509_ = stack[10].m_obj;
lean_object* v___y_510_ = stack[11].m_obj;
lean_object* v_res_534_;
v_res_534_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(v_a_499_, v_snd_500_, v_x_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed(lean_object* v_a_535_, lean_object* v_snd_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(v_a_535_, v_snd_536_, v_x_537_, v_x_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v_x_537_);
lean_dec_ref(v_a_535_);
return v_res_548_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_k_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
v___x_560_ = lean_apply_10(v_k_549_, v_b_554_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, lean_box(0));
return v___x_560_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_549_ = stack[0].m_obj;
lean_object* v___y_550_ = stack[1].m_obj;
lean_object* v___y_551_ = stack[2].m_obj;
lean_object* v___y_552_ = stack[3].m_obj;
lean_object* v___y_553_ = stack[4].m_obj;
lean_object* v_b_554_ = stack[5].m_obj;
lean_object* v___y_555_ = stack[6].m_obj;
lean_object* v___y_556_ = stack[7].m_obj;
lean_object* v___y_557_ = stack[8].m_obj;
lean_object* v___y_558_ = stack[9].m_obj;
lean_object* v_res_561_;
v_res_561_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(v_k_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v_b_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
stack->m_obj
 = v_res_561_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v_k_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(v_k_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v_b_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_573_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(lean_object* v_name_574_, uint8_t v_bi_575_, lean_object* v_type_576_, lean_object* v_k_577_, uint8_t v_kind_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
v___f_588_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_588_, 0, v_k_577_);
lean_closure_set(v___f_588_, 1, v___y_579_);
lean_closure_set(v___f_588_, 2, v___y_580_);
lean_closure_set(v___f_588_, 3, v___y_581_);
lean_closure_set(v___f_588_, 4, v___y_582_);
v___x_589_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_574_, v_bi_575_, v_type_576_, v___f_588_, v_kind_578_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
return v___x_589_;
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_574_ = stack[0].m_obj;
uint8_t v_bi_575_ = stack[1].m_num;
lean_object* v_type_576_ = stack[2].m_obj;
lean_object* v_k_577_ = stack[3].m_obj;
uint8_t v_kind_578_ = stack[4].m_num;
lean_object* v___y_579_ = stack[5].m_obj;
lean_object* v___y_580_ = stack[6].m_obj;
lean_object* v___y_581_ = stack[7].m_obj;
lean_object* v___y_582_ = stack[8].m_obj;
lean_object* v___y_583_ = stack[9].m_obj;
lean_object* v___y_584_ = stack[10].m_obj;
lean_object* v___y_585_ = stack[11].m_obj;
lean_object* v___y_586_ = stack[12].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_574_, v_bi_575_, v_type_576_, v_k_577_, v_kind_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_name_599_, lean_object* v_bi_600_, lean_object* v_type_601_, lean_object* v_k_602_, lean_object* v_kind_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v_bi_boxed_613_; uint8_t v_kind_boxed_614_; lean_object* v_res_615_; 
v_bi_boxed_613_ = lean_unbox(v_bi_600_);
v_kind_boxed_614_ = lean_unbox(v_kind_603_);
v_res_615_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_599_, v_bi_boxed_613_, v_type_601_, v_k_602_, v_kind_boxed_614_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_615_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(lean_object* v_name_616_, lean_object* v_type_617_, lean_object* v_k_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v___x_628_ = 0;
v___x_629_ = 0;
v___x_630_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_616_, v___x_628_, v_type_617_, v_k_618_, v___x_629_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_630_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_616_ = stack[0].m_obj;
lean_object* v_type_617_ = stack[1].m_obj;
lean_object* v_k_618_ = stack[2].m_obj;
lean_object* v___y_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v___y_622_ = stack[6].m_obj;
lean_object* v___y_623_ = stack[7].m_obj;
lean_object* v___y_624_ = stack[8].m_obj;
lean_object* v___y_625_ = stack[9].m_obj;
lean_object* v___y_626_ = stack[10].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_616_, v_type_617_, v_k_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg___boxed(lean_object* v_name_632_, lean_object* v_type_633_, lean_object* v_k_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_632_, v_type_633_, v_k_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_644_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(lean_object* v_a_645_, lean_object* v_snd_646_, lean_object* v_k_647_, lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_00_u03c3s_653_, lean_object* v_hyp_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_h_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_lctx_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; 
v_lctx_667_ = lean_ctor_get(v___y_662_, 2);
lean_inc_ref(v_a_645_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_a_645_);
v___x_669_ = 0;
lean_inc_ref(v_h_657_);
lean_inc_ref(v_lctx_667_);
v___x_670_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_646_, v_lctx_667_, v_h_657_, v___x_668_, v___x_669_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; 
lean_dec_ref_known(v___x_670_, 1);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
lean_inc_ref(v_h_657_);
lean_inc_ref(v_a_645_);
v___x_671_ = lean_apply_11(v_k_647_, v_a_645_, v_h_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, lean_box(0));
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v_snd_673_; lean_object* v_fst_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_729_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v_snd_673_ = lean_ctor_get(v_a_672_, 1);
v_fst_674_ = lean_ctor_get(v_a_672_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_729_ == 0)
{
v___x_676_ = v_a_672_;
v_isShared_677_ = v_isSharedCheck_729_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snd_673_);
lean_inc(v_fst_674_);
lean_dec(v_a_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_729_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_fst_678_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_728_; 
v_fst_678_ = lean_ctor_get(v_snd_673_, 0);
v_snd_679_ = lean_ctor_get(v_snd_673_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_snd_673_);
if (v_isSharedCheck_728_ == 0)
{
v___x_681_ = v_snd_673_;
v_isShared_682_ = v_isSharedCheck_728_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_inc(v_fst_678_);
lean_dec(v_snd_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_728_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; 
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_mk_empty_array_with_capacity(v___x_683_);
v___x_685_ = lean_array_push(v___x_684_, v_h_657_);
v___x_686_ = 1;
v___x_687_ = 1;
v___x_688_ = l_Lean_Meta_mkLambdaFVars(v___x_685_, v_snd_679_, v___x_669_, v___x_686_, v___x_669_, v___x_686_, v___x_687_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec_ref(v___x_685_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_719_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_719_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_719_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_719_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_u_693_; lean_object* v_00_u03c3s_694_; lean_object* v_hyps_695_; lean_object* v_target_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_718_; 
v_u_693_ = lean_ctor_get(v_fst_678_, 0);
v_00_u03c3s_694_ = lean_ctor_get(v_fst_678_, 1);
v_hyps_695_ = lean_ctor_get(v_fst_678_, 2);
v_target_696_ = lean_ctor_get(v_fst_678_, 3);
v_isSharedCheck_718_ = !lean_is_exclusive(v_fst_678_);
if (v_isSharedCheck_718_ == 0)
{
v___x_698_ = v_fst_678_;
v_isShared_699_ = v_isSharedCheck_718_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_target_696_);
lean_inc(v_hyps_695_);
lean_inc(v_00_u03c3s_694_);
lean_inc(v_u_693_);
lean_dec(v_fst_678_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_718_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_prf_704_; lean_object* v___x_705_; lean_object* v_goal_707_; 
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1));
v___x_702_ = l_Lean_Name_mkStr6(v___x_648_, v___x_649_, v___x_650_, v___x_651_, v___x_700_, v___x_701_);
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_652_);
lean_inc_ref(v_target_696_);
lean_inc_ref(v_hyp_654_);
lean_inc_ref(v_hyps_695_);
lean_inc_ref(v_00_u03c3s_653_);
v_prf_704_ = l_Lean_mkApp7(v___x_703_, v_00_u03c3s_653_, v_hyps_695_, v_hyp_654_, v_target_696_, v_a_645_, v_a_655_, v_a_689_);
v___x_705_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_656_, v_00_u03c3s_653_, v_hyps_695_, v_hyp_654_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v___x_705_);
v_goal_707_ = v___x_698_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_u_693_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_00_u03c3s_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_target_696_);
v_goal_707_ = v_reuseFailAlloc_717_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_prf_704_);
lean_ctor_set(v___x_681_, 0, v_goal_707_);
v___x_709_ = v___x_681_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_goal_707_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_prf_704_);
v___x_709_ = v_reuseFailAlloc_716_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_709_);
v___x_711_ = v___x_676_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_674_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_711_);
v___x_713_ = v___x_691_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_del_object(v___x_681_);
lean_dec(v_fst_678_);
lean_del_object(v___x_676_);
lean_dec(v_fst_674_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec_ref(v_hyp_654_);
lean_dec_ref(v_00_u03c3s_653_);
lean_dec(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_648_);
lean_dec_ref(v_a_645_);
v_a_720_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_688_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_688_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec_ref(v_hyp_654_);
lean_dec_ref(v_00_u03c3s_653_);
lean_dec(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_648_);
lean_dec_ref(v_a_645_);
return v___x_671_;
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_h_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec_ref(v_hyp_654_);
lean_dec_ref(v_00_u03c3s_653_);
lean_dec(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_648_);
lean_dec_ref(v_k_647_);
lean_dec_ref(v_a_645_);
v_a_730_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_670_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_670_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_645_ = stack[0].m_obj;
lean_object* v_snd_646_ = stack[1].m_obj;
lean_object* v_k_647_ = stack[2].m_obj;
lean_object* v___x_648_ = stack[3].m_obj;
lean_object* v___x_649_ = stack[4].m_obj;
lean_object* v___x_650_ = stack[5].m_obj;
lean_object* v___x_651_ = stack[6].m_obj;
lean_object* v___x_652_ = stack[7].m_obj;
lean_object* v_00_u03c3s_653_ = stack[8].m_obj;
lean_object* v_hyp_654_ = stack[9].m_obj;
lean_object* v_a_655_ = stack[10].m_obj;
lean_object* v_a_656_ = stack[11].m_obj;
lean_object* v_h_657_ = stack[12].m_obj;
lean_object* v___y_658_ = stack[13].m_obj;
lean_object* v___y_659_ = stack[14].m_obj;
lean_object* v___y_660_ = stack[15].m_obj;
lean_object* v___y_661_ = stack[16].m_obj;
lean_object* v___y_662_ = stack[17].m_obj;
lean_object* v___y_663_ = stack[18].m_obj;
lean_object* v___y_664_ = stack[19].m_obj;
lean_object* v___y_665_ = stack[20].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(v_a_645_, v_snd_646_, v_k_647_, v___x_648_, v___x_649_, v___x_650_, v___x_651_, v___x_652_, v_00_u03c3s_653_, v_hyp_654_, v_a_655_, v_a_656_, v_h_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_739_ = _args[0];
lean_object* v_snd_740_ = _args[1];
lean_object* v_k_741_ = _args[2];
lean_object* v___x_742_ = _args[3];
lean_object* v___x_743_ = _args[4];
lean_object* v___x_744_ = _args[5];
lean_object* v___x_745_ = _args[6];
lean_object* v___x_746_ = _args[7];
lean_object* v_00_u03c3s_747_ = _args[8];
lean_object* v_hyp_748_ = _args[9];
lean_object* v_a_749_ = _args[10];
lean_object* v_a_750_ = _args[11];
lean_object* v_h_751_ = _args[12];
lean_object* v___y_752_ = _args[13];
lean_object* v___y_753_ = _args[14];
lean_object* v___y_754_ = _args[15];
lean_object* v___y_755_ = _args[16];
lean_object* v___y_756_ = _args[17];
lean_object* v___y_757_ = _args[18];
lean_object* v___y_758_ = _args[19];
lean_object* v___y_759_ = _args[20];
lean_object* v___y_760_ = _args[21];
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(v_a_739_, v_snd_740_, v_k_741_, v___x_742_, v___x_743_, v___x_744_, v___x_745_, v___x_746_, v_00_u03c3s_747_, v_hyp_748_, v_a_749_, v_a_750_, v_h_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_761_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(lean_object* v_00_u03c3s_762_, lean_object* v_hyp_763_, lean_object* v_name_764_, lean_object* v_k_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_mkFreshLevelMVar(v___y_770_, v___y_771_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_778_ = 0;
v___x_779_ = lean_box(0);
v___x_780_ = l_Lean_Meta_mkFreshExprMVar(v___x_777_, v___x_778_, v___x_779_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_n(v_a_781_, 2);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_787_ = lean_box(0);
lean_inc(v_a_776_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_776_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
lean_inc_ref(v___x_788_);
v___x_789_ = l_Lean_mkConst(v___x_786_, v___x_788_);
lean_inc_ref(v_hyp_763_);
lean_inc_ref(v_00_u03c3s_762_);
v___x_790_ = l_Lean_mkApp3(v___x_789_, v_00_u03c3s_762_, v_hyp_763_, v_a_781_);
v___x_791_ = lean_box(0);
v___x_792_ = l_Lean_Meta_synthInstance(v___x_790_, v___x_791_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_764_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v_fst_796_; lean_object* v_snd_797_; lean_object* v___f_798_; lean_object* v___x_799_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v_fst_796_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_fst_796_);
v_snd_797_ = lean_ctor_get(v_a_795_, 1);
lean_inc(v_snd_797_);
lean_dec(v_a_795_);
lean_inc(v_a_781_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed), 22, 12);
lean_closure_set(v___f_798_, 0, v_a_781_);
lean_closure_set(v___f_798_, 1, v_snd_797_);
lean_closure_set(v___f_798_, 2, v_k_765_);
lean_closure_set(v___f_798_, 3, v___x_782_);
lean_closure_set(v___f_798_, 4, v___x_783_);
lean_closure_set(v___f_798_, 5, v___x_784_);
lean_closure_set(v___f_798_, 6, v___x_785_);
lean_closure_set(v___f_798_, 7, v___x_788_);
lean_closure_set(v___f_798_, 8, v_00_u03c3s_762_);
lean_closure_set(v___f_798_, 9, v_hyp_763_);
lean_closure_set(v___f_798_, 10, v_a_793_);
lean_closure_set(v___f_798_, 11, v_a_776_);
v___x_799_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_fst_796_, v_a_781_, v___f_798_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_799_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_a_793_);
lean_dec_ref_known(v___x_788_, 2);
lean_dec(v_a_781_);
lean_dec(v_a_776_);
lean_dec_ref(v_k_765_);
lean_dec_ref(v_hyp_763_);
lean_dec_ref(v_00_u03c3s_762_);
v_a_800_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_794_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_794_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref_known(v___x_788_, 2);
lean_dec(v_a_781_);
lean_dec(v_a_776_);
lean_dec_ref(v_k_765_);
lean_dec(v_name_764_);
lean_dec_ref(v_hyp_763_);
lean_dec_ref(v_00_u03c3s_762_);
v_a_808_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_792_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_792_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_776_);
lean_dec_ref(v_k_765_);
lean_dec(v_name_764_);
lean_dec_ref(v_hyp_763_);
lean_dec_ref(v_00_u03c3s_762_);
v_a_816_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_780_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_780_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec_ref(v_k_765_);
lean_dec(v_name_764_);
lean_dec_ref(v_hyp_763_);
lean_dec_ref(v_00_u03c3s_762_);
v_a_824_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_775_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_775_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c3s_762_ = stack[0].m_obj;
lean_object* v_hyp_763_ = stack[1].m_obj;
lean_object* v_name_764_ = stack[2].m_obj;
lean_object* v_k_765_ = stack[3].m_obj;
lean_object* v___y_766_ = stack[4].m_obj;
lean_object* v___y_767_ = stack[5].m_obj;
lean_object* v___y_768_ = stack[6].m_obj;
lean_object* v___y_769_ = stack[7].m_obj;
lean_object* v___y_770_ = stack[8].m_obj;
lean_object* v___y_771_ = stack[9].m_obj;
lean_object* v___y_772_ = stack[10].m_obj;
lean_object* v___y_773_ = stack[11].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_762_, v_hyp_763_, v_name_764_, v_k_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___boxed(lean_object* v_00_u03c3s_833_, lean_object* v_hyp_834_, lean_object* v_name_835_, lean_object* v_k_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_833_, v_hyp_834_, v_name_835_, v_k_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_ks_851_; lean_object* v_vs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_876_; 
v_ks_851_ = lean_ctor_get(v_x_847_, 0);
v_vs_852_ = lean_ctor_get(v_x_847_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_876_ == 0)
{
v___x_854_ = v_x_847_;
v_isShared_855_ = v_isSharedCheck_876_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_vs_852_);
lean_inc(v_ks_851_);
lean_dec(v_x_847_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_876_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_array_get_size(v_ks_851_);
v___x_857_ = lean_nat_dec_lt(v_x_848_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_x_848_);
v___x_858_ = lean_array_push(v_ks_851_, v_x_849_);
v___x_859_ = lean_array_push(v_vs_852_, v_x_850_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_859_);
lean_ctor_set(v___x_854_, 0, v___x_858_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v_k_x27_863_; uint8_t v___x_864_; 
v_k_x27_863_ = lean_array_fget_borrowed(v_ks_851_, v_x_848_);
v___x_864_ = l_Lean_instBEqMVarId_beq(v_x_849_, v_k_x27_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_866_; 
if (v_isShared_855_ == 0)
{
v___x_866_ = v___x_854_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_ks_851_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_vs_852_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_x_848_, v___x_867_);
lean_dec(v_x_848_);
v_x_847_ = v___x_866_;
v_x_848_ = v___x_868_;
goto _start;
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_871_ = lean_array_fset(v_ks_851_, v_x_848_, v_x_849_);
v___x_872_ = lean_array_fset(v_vs_852_, v_x_848_, v_x_850_);
lean_dec(v_x_848_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_872_);
lean_ctor_set(v___x_854_, 0, v___x_871_);
v___x_874_ = v___x_854_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(lean_object* v_n_877_, lean_object* v_k_878_, lean_object* v_v_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_n_877_, v___x_880_, v_k_878_, v_v_879_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_882_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(lean_object* v_x_883_, size_t v_x_884_, size_t v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
lean_object* v_es_888_; size_t v___x_889_; size_t v___x_890_; lean_object* v_j_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_es_888_ = lean_ctor_get(v_x_883_, 0);
v___x_889_ = ((size_t)31ULL);
v___x_890_ = lean_usize_land(v_x_884_, v___x_889_);
v_j_891_ = lean_usize_to_nat(v___x_890_);
v___x_892_ = lean_array_get_size(v_es_888_);
v___x_893_ = lean_nat_dec_lt(v_j_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_dec(v_j_891_);
lean_dec(v_x_887_);
lean_dec(v_x_886_);
return v_x_883_;
}
else
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_932_; 
lean_inc_ref(v_es_888_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_x_883_, 0);
lean_dec(v_unused_933_);
v___x_895_ = v_x_883_;
v_isShared_896_ = v_isSharedCheck_932_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_x_883_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_932_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_v_897_; lean_object* v___x_898_; lean_object* v_xs_x27_899_; lean_object* v___y_901_; 
v_v_897_ = lean_array_fget(v_es_888_, v_j_891_);
v___x_898_ = lean_box(0);
v_xs_x27_899_ = lean_array_fset(v_es_888_, v_j_891_, v___x_898_);
switch(lean_obj_tag(v_v_897_))
{
case 0:
{
lean_object* v_key_906_; lean_object* v_val_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v_key_906_ = lean_ctor_get(v_v_897_, 0);
v_val_907_ = lean_ctor_get(v_v_897_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_v_897_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v_v_897_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_val_907_);
lean_inc(v_key_906_);
lean_dec(v_v_897_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_instBEqMVarId_beq(v_x_886_, v_key_906_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_del_object(v___x_909_);
v___x_912_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_906_, v_val_907_, v_x_886_, v_x_887_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___y_901_ = v___x_913_;
goto v___jp_900_;
}
else
{
lean_object* v___x_915_; 
lean_dec(v_val_907_);
lean_dec(v_key_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_x_887_);
lean_ctor_set(v___x_909_, 0, v_x_886_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_x_886_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_x_887_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v___y_901_ = v___x_915_;
goto v___jp_900_;
}
}
}
}
case 1:
{
lean_object* v_node_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_930_; 
v_node_918_ = lean_ctor_get(v_v_897_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_v_897_);
if (v_isSharedCheck_930_ == 0)
{
v___x_920_ = v_v_897_;
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_node_918_);
lean_dec(v_v_897_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_922_ = ((size_t)5ULL);
v___x_923_ = lean_usize_shift_right(v_x_884_, v___x_922_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_x_885_, v___x_924_);
v___x_926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_node_918_, v___x_923_, v___x_925_, v_x_886_, v_x_887_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_926_);
v___x_928_ = v___x_920_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
v___y_901_ = v___x_928_;
goto v___jp_900_;
}
}
}
default: 
{
lean_object* v___x_931_; 
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_x_886_);
lean_ctor_set(v___x_931_, 1, v_x_887_);
v___y_901_ = v___x_931_;
goto v___jp_900_;
}
}
v___jp_900_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_array_fset(v_xs_x27_899_, v_j_891_, v___y_901_);
lean_dec(v_j_891_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_902_);
v___x_904_ = v___x_895_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
else
{
lean_object* v_ks_934_; lean_object* v_vs_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_953_; 
v_ks_934_ = lean_ctor_get(v_x_883_, 0);
v_vs_935_ = lean_ctor_get(v_x_883_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_953_ == 0)
{
v___x_937_ = v_x_883_;
v_isShared_938_ = v_isSharedCheck_953_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_vs_935_);
lean_inc(v_ks_934_);
lean_dec(v_x_883_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_953_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_ks_934_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_vs_935_);
v___x_940_ = v_reuseFailAlloc_952_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v_newNode_941_; size_t v___x_942_; uint8_t v___x_943_; 
v_newNode_941_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v___x_940_, v_x_886_, v_x_887_);
v___x_942_ = ((size_t)7ULL);
v___x_943_ = lean_usize_dec_le(v___x_942_, v_x_885_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_941_);
v___x_945_ = lean_unsigned_to_nat(4u);
v___x_946_ = lean_nat_dec_lt(v___x_944_, v___x_945_);
lean_dec(v___x_944_);
if (v___x_946_ == 0)
{
lean_object* v_ks_947_; lean_object* v_vs_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_ks_947_ = lean_ctor_get(v_newNode_941_, 0);
lean_inc_ref(v_ks_947_);
v_vs_948_ = lean_ctor_get(v_newNode_941_, 1);
lean_inc_ref(v_vs_948_);
lean_dec_ref(v_newNode_941_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0);
v___x_951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_x_885_, v_ks_947_, v_vs_948_, v___x_949_, v___x_950_);
lean_dec_ref(v_vs_948_);
lean_dec_ref(v_ks_947_);
return v___x_951_;
}
else
{
return v_newNode_941_;
}
}
else
{
return v_newNode_941_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_883_ = stack[0].m_obj;
size_t v_x_884_ = stack[1].m_num;
size_t v_x_885_ = stack[2].m_num;
lean_object* v_x_886_ = stack[3].m_obj;
lean_object* v_x_887_ = stack[4].m_obj;
lean_object* v_res_954_;
v_res_954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_883_, v_x_884_, v_x_885_, v_x_886_, v_x_887_);
stack->m_obj
 = v_res_954_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(size_t v_depth_955_, lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_i_958_, lean_object* v_entries_959_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_array_get_size(v_keys_956_);
v___x_961_ = lean_nat_dec_lt(v_i_958_, v___x_960_);
if (v___x_961_ == 0)
{
lean_dec(v_i_958_);
return v_entries_959_;
}
else
{
lean_object* v_k_962_; lean_object* v_v_963_; uint64_t v___x_964_; size_t v_h_965_; size_t v___x_966_; lean_object* v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v_h_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_k_962_ = lean_array_fget_borrowed(v_keys_956_, v_i_958_);
v_v_963_ = lean_array_fget_borrowed(v_vals_957_, v_i_958_);
v___x_964_ = l_Lean_instHashableMVarId_hash(v_k_962_);
v_h_965_ = lean_uint64_to_usize(v___x_964_);
v___x_966_ = ((size_t)5ULL);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_sub(v_depth_955_, v___x_968_);
v___x_970_ = lean_usize_mul(v___x_966_, v___x_969_);
v_h_971_ = lean_usize_shift_right(v_h_965_, v___x_970_);
v___x_972_ = lean_nat_add(v_i_958_, v___x_967_);
lean_dec(v_i_958_);
lean_inc(v_v_963_);
lean_inc(v_k_962_);
v___x_973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_entries_959_, v_h_971_, v_depth_955_, v_k_962_, v_v_963_);
v_i_958_ = v___x_972_;
v_entries_959_ = v___x_973_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_955_ = stack[0].m_num;
lean_object* v_keys_956_ = stack[1].m_obj;
lean_object* v_vals_957_ = stack[2].m_obj;
lean_object* v_i_958_ = stack[3].m_obj;
lean_object* v_entries_959_ = stack[4].m_obj;
lean_object* v_res_975_;
v_res_975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_955_, v_keys_956_, v_vals_957_, v_i_958_, v_entries_959_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_976_, lean_object* v_keys_977_, lean_object* v_vals_978_, lean_object* v_i_979_, lean_object* v_entries_980_){
_start:
{
size_t v_depth_boxed_981_; lean_object* v_res_982_; 
v_depth_boxed_981_ = lean_unbox_usize(v_depth_976_);
lean_dec(v_depth_976_);
v_res_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_boxed_981_, v_keys_977_, v_vals_978_, v_i_979_, v_entries_980_);
lean_dec_ref(v_vals_978_);
lean_dec_ref(v_keys_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
size_t v_x_10253__boxed_988_; size_t v_x_10254__boxed_989_; lean_object* v_res_990_; 
v_x_10253__boxed_988_ = lean_unbox_usize(v_x_984_);
lean_dec(v_x_984_);
v_x_10254__boxed_989_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_res_990_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_983_, v_x_10253__boxed_988_, v_x_10254__boxed_989_, v_x_986_, v_x_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
uint64_t v___x_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_994_ = l_Lean_instHashableMVarId_hash(v_x_992_);
v___x_995_ = lean_uint64_to_usize(v___x_994_);
v___x_996_ = ((size_t)1ULL);
v___x_997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_991_, v___x_995_, v___x_996_, v_x_992_, v_x_993_);
return v___x_997_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(lean_object* v_mvarId_998_, lean_object* v_val_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_mctx_1003_; lean_object* v_cache_1004_; lean_object* v_zetaDeltaFVarIds_1005_; lean_object* v_postponed_1006_; lean_object* v_diag_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1037_; 
v___x_1002_ = lean_st_ref_take(v___y_1000_);
v_mctx_1003_ = lean_ctor_get(v___x_1002_, 0);
v_cache_1004_ = lean_ctor_get(v___x_1002_, 1);
v_zetaDeltaFVarIds_1005_ = lean_ctor_get(v___x_1002_, 2);
v_postponed_1006_ = lean_ctor_get(v___x_1002_, 3);
v_diag_1007_ = lean_ctor_get(v___x_1002_, 4);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1009_ = v___x_1002_;
v_isShared_1010_ = v_isSharedCheck_1037_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_diag_1007_);
lean_inc(v_postponed_1006_);
lean_inc(v_zetaDeltaFVarIds_1005_);
lean_inc(v_cache_1004_);
lean_inc(v_mctx_1003_);
lean_dec(v___x_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1037_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_depth_1011_; lean_object* v_levelAssignDepth_1012_; lean_object* v_lmvarCounter_1013_; lean_object* v_mvarCounter_1014_; lean_object* v_lDecls_1015_; lean_object* v_decls_1016_; lean_object* v_userNames_1017_; lean_object* v_lAssignment_1018_; lean_object* v_eAssignment_1019_; lean_object* v_dAssignment_1020_; lean_object* v_instanceTypedMVars_1021_; lean_object* v_synthNormMemo_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1036_; 
v_depth_1011_ = lean_ctor_get(v_mctx_1003_, 0);
v_levelAssignDepth_1012_ = lean_ctor_get(v_mctx_1003_, 1);
v_lmvarCounter_1013_ = lean_ctor_get(v_mctx_1003_, 2);
v_mvarCounter_1014_ = lean_ctor_get(v_mctx_1003_, 3);
v_lDecls_1015_ = lean_ctor_get(v_mctx_1003_, 4);
v_decls_1016_ = lean_ctor_get(v_mctx_1003_, 5);
v_userNames_1017_ = lean_ctor_get(v_mctx_1003_, 6);
v_lAssignment_1018_ = lean_ctor_get(v_mctx_1003_, 7);
v_eAssignment_1019_ = lean_ctor_get(v_mctx_1003_, 8);
v_dAssignment_1020_ = lean_ctor_get(v_mctx_1003_, 9);
v_instanceTypedMVars_1021_ = lean_ctor_get(v_mctx_1003_, 10);
v_synthNormMemo_1022_ = lean_ctor_get(v_mctx_1003_, 11);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_mctx_1003_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1024_ = v_mctx_1003_;
v_isShared_1025_ = v_isSharedCheck_1036_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_synthNormMemo_1022_);
lean_inc(v_instanceTypedMVars_1021_);
lean_inc(v_dAssignment_1020_);
lean_inc(v_eAssignment_1019_);
lean_inc(v_lAssignment_1018_);
lean_inc(v_userNames_1017_);
lean_inc(v_decls_1016_);
lean_inc(v_lDecls_1015_);
lean_inc(v_mvarCounter_1014_);
lean_inc(v_lmvarCounter_1013_);
lean_inc(v_levelAssignDepth_1012_);
lean_inc(v_depth_1011_);
lean_dec(v_mctx_1003_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1036_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_1019_, v_mvarId_998_, v_val_999_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 8, v___x_1027_);
v___x_1029_ = v___x_1024_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_depth_1011_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_levelAssignDepth_1012_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_lmvarCounter_1013_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_mvarCounter_1014_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_lDecls_1015_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_decls_1016_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_userNames_1017_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v_lAssignment_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 9, v_dAssignment_1020_);
lean_ctor_set(v_reuseFailAlloc_1035_, 10, v_instanceTypedMVars_1021_);
lean_ctor_set(v_reuseFailAlloc_1035_, 11, v_synthNormMemo_1022_);
v___x_1029_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1029_);
v___x_1031_ = v___x_1009_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_cache_1004_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_zetaDeltaFVarIds_1005_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_postponed_1006_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_diag_1007_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_st_ref_put(v___y_1000_, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1026_);
return v___x_1033_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_998_ = stack[0].m_obj;
lean_object* v_val_999_ = stack[1].m_obj;
lean_object* v___y_1000_ = stack[2].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_mvarId_998_, v_val_999_, v___y_1000_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg___boxed(lean_object* v_mvarId_1039_, lean_object* v_val_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_mvarId_1039_, v_val_1040_, v___y_1041_);
lean_dec(v___y_1041_);
return v_res_1043_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(lean_object* v_snd_1045_, lean_object* v_hyp_1046_, lean_object* v___x_1047_, lean_object* v_fst_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
lean_inc(v_hyp_1046_);
lean_inc_ref(v_snd_1045_);
v___x_1058_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_1045_, v_hyp_1046_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v_ref_1060_; lean_object* v_00_u03c3s_1061_; lean_object* v_focusHyp_1062_; lean_object* v___f_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_n(v_a_1059_, 2);
lean_dec_ref_known(v___x_1058_, 1);
v_ref_1060_ = lean_ctor_get(v___y_1055_, 2);
v_00_u03c3s_1061_ = lean_ctor_get(v_snd_1045_, 1);
v_focusHyp_1062_ = lean_ctor_get(v_a_1059_, 0);
lean_inc_ref(v_snd_1045_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1063_, 0, v_a_1059_);
lean_closure_set(v___f_1063_, 1, v_snd_1045_);
v___x_1064_ = 0;
v___x_1065_ = l_Lean_SourceInfo_fromRef(v_ref_1060_, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0));
v___x_1067_ = l_Lean_Name_mkStr2(v___x_1047_, v___x_1066_);
v___x_1068_ = l_Lean_Syntax_node1(v___x_1065_, v___x_1067_, v_hyp_1046_);
lean_inc_ref(v_focusHyp_1062_);
lean_inc_ref(v_00_u03c3s_1061_);
v___x_1069_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_1061_, v_focusHyp_1062_, v___x_1068_, v___f_1063_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_snd_1071_; lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1085_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v_snd_1071_ = lean_ctor_get(v_a_1070_, 1);
lean_inc(v_snd_1071_);
v_fst_1072_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_fst_1072_);
lean_dec(v_a_1070_);
v_snd_1073_ = lean_ctor_get(v_snd_1071_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_snd_1071_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_snd_1071_, 0);
lean_dec(v_unused_1086_);
v___x_1075_ = v_snd_1071_;
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_dec(v_snd_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1077_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_1059_, v_snd_1045_, v_snd_1073_);
v___x_1078_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_1048_, v___x_1077_, v___y_1054_);
lean_dec_ref(v___x_1078_);
v___x_1079_ = l_Lean_Expr_mvarId_x21(v_fst_1072_);
lean_dec(v_fst_1072_);
v___x_1080_ = lean_box(0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 1, v___x_1080_);
lean_ctor_set(v___x_1075_, 0, v___x_1079_);
v___x_1082_ = v___x_1075_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1082_, v___y_1050_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v_a_1059_);
lean_dec(v_fst_1048_);
lean_dec_ref(v_snd_1045_);
v_a_1087_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1069_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1069_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_fst_1048_);
lean_dec_ref(v___x_1047_);
lean_dec(v_hyp_1046_);
lean_dec_ref(v_snd_1045_);
v_a_1095_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1058_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1058_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1045_ = stack[0].m_obj;
lean_object* v_hyp_1046_ = stack[1].m_obj;
lean_object* v___x_1047_ = stack[2].m_obj;
lean_object* v_fst_1048_ = stack[3].m_obj;
lean_object* v___y_1049_ = stack[4].m_obj;
lean_object* v___y_1050_ = stack[5].m_obj;
lean_object* v___y_1051_ = stack[6].m_obj;
lean_object* v___y_1052_ = stack[7].m_obj;
lean_object* v___y_1053_ = stack[8].m_obj;
lean_object* v___y_1054_ = stack[9].m_obj;
lean_object* v___y_1055_ = stack[10].m_obj;
lean_object* v___y_1056_ = stack[11].m_obj;
lean_object* v_res_1103_;
v_res_1103_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(v_snd_1045_, v_hyp_1046_, v___x_1047_, v_fst_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
stack->m_obj
 = v_res_1103_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed(lean_object* v_snd_1104_, lean_object* v_hyp_1105_, lean_object* v___x_1106_, lean_object* v_fst_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(v_snd_1104_, v_hyp_1105_, v___x_1106_, v_fst_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1117_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(lean_object* v_x_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0));
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3));
lean_inc(v_x_1126_);
v___x_1138_ = l_Lean_Syntax_isOfKind(v_x_1126_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec(v_x_1126_);
v___x_1139_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v_hyp_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_unsigned_to_nat(1u);
v_hyp_1141_ = l_Lean_Syntax_getArg(v_x_1126_, v___x_1140_);
lean_dec(v_x_1126_);
v___x_1142_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1128_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v_fst_1144_ = lean_ctor_get(v_a_1143_, 0);
lean_inc_n(v_fst_1144_, 2);
v_snd_1145_ = lean_ctor_get(v_a_1143_, 1);
lean_inc(v_snd_1145_);
lean_dec(v_a_1143_);
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1146_, 0, v_snd_1145_);
lean_closure_set(v___f_1146_, 1, v_hyp_1141_);
lean_closure_set(v___f_1146_, 2, v___x_1136_);
lean_closure_set(v___f_1146_, 3, v_fst_1144_);
v___x_1147_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_1144_, v___f_1146_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1147_;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_hyp_1141_);
v_a_1148_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1142_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1142_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPure_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1126_ = stack[0].m_obj;
lean_object* v_a_1127_ = stack[1].m_obj;
lean_object* v_a_1128_ = stack[2].m_obj;
lean_object* v_a_1129_ = stack[3].m_obj;
lean_object* v_a_1130_ = stack[4].m_obj;
lean_object* v_a_1131_ = stack[5].m_obj;
lean_object* v_a_1132_ = stack[6].m_obj;
lean_object* v_a_1133_ = stack[7].m_obj;
lean_object* v_a_1134_ = stack[8].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(v_x_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed(lean_object* v_x_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(v_x_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1167_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(lean_object* v_00_u03b1_1168_, lean_object* v_00_u03c3s_1169_, lean_object* v_hyp_1170_, lean_object* v_name_1171_, lean_object* v_k_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_1169_, v_hyp_1170_, v_name_1171_, v_k_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c3s_1169_ = stack[1].m_obj;
lean_object* v_hyp_1170_ = stack[2].m_obj;
lean_object* v_name_1171_ = stack[3].m_obj;
lean_object* v_k_1172_ = stack[4].m_obj;
lean_object* v___y_1173_ = stack[5].m_obj;
lean_object* v___y_1174_ = stack[6].m_obj;
lean_object* v___y_1175_ = stack[7].m_obj;
lean_object* v___y_1176_ = stack[8].m_obj;
lean_object* v___y_1177_ = stack[9].m_obj;
lean_object* v___y_1178_ = stack[10].m_obj;
lean_object* v___y_1179_ = stack[11].m_obj;
lean_object* v___y_1180_ = stack[12].m_obj;
lean_object* v_res_1183_;
v_res_1183_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(lean_box(0), v_00_u03c3s_1169_, v_hyp_1170_, v_name_1171_, v_k_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
stack->m_obj
 = v_res_1183_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03c3s_1185_, lean_object* v_hyp_1186_, lean_object* v_name_1187_, lean_object* v_k_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(v_00_u03b1_1184_, v_00_u03c3s_1185_, v_hyp_1186_, v_name_1187_, v_k_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1198_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(lean_object* v_mvarId_1199_, lean_object* v_val_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_mvarId_1199_, v_val_1200_, v___y_1206_);
return v___x_1210_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1199_ = stack[0].m_obj;
lean_object* v_val_1200_ = stack[1].m_obj;
lean_object* v___y_1201_ = stack[2].m_obj;
lean_object* v___y_1202_ = stack[3].m_obj;
lean_object* v___y_1203_ = stack[4].m_obj;
lean_object* v___y_1204_ = stack[5].m_obj;
lean_object* v___y_1205_ = stack[6].m_obj;
lean_object* v___y_1206_ = stack[7].m_obj;
lean_object* v___y_1207_ = stack[8].m_obj;
lean_object* v___y_1208_ = stack[9].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(v_mvarId_1199_, v_val_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___boxed(lean_object* v_mvarId_1212_, lean_object* v_val_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(v_mvarId_1212_, v_val_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1223_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(lean_object* v_00_u03b1_1224_, lean_object* v_name_1225_, uint8_t v_bi_1226_, lean_object* v_type_1227_, lean_object* v_k_1228_, uint8_t v_kind_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_1225_, v_bi_1226_, v_type_1227_, v_k_1228_, v_kind_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1225_ = stack[1].m_obj;
uint8_t v_bi_1226_ = stack[2].m_num;
lean_object* v_type_1227_ = stack[3].m_obj;
lean_object* v_k_1228_ = stack[4].m_obj;
uint8_t v_kind_1229_ = stack[5].m_num;
lean_object* v___y_1230_ = stack[6].m_obj;
lean_object* v___y_1231_ = stack[7].m_obj;
lean_object* v___y_1232_ = stack[8].m_obj;
lean_object* v___y_1233_ = stack[9].m_obj;
lean_object* v___y_1234_ = stack[10].m_obj;
lean_object* v___y_1235_ = stack[11].m_obj;
lean_object* v___y_1236_ = stack[12].m_obj;
lean_object* v___y_1237_ = stack[13].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(lean_box(0), v_name_1225_, v_bi_1226_, v_type_1227_, v_k_1228_, v_kind_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1241_, lean_object* v_name_1242_, lean_object* v_bi_1243_, lean_object* v_type_1244_, lean_object* v_k_1245_, lean_object* v_kind_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_bi_boxed_1256_; uint8_t v_kind_boxed_1257_; lean_object* v_res_1258_; 
v_bi_boxed_1256_ = lean_unbox(v_bi_1243_);
v_kind_boxed_1257_ = lean_unbox(v_kind_1246_);
v_res_1258_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(v_00_u03b1_1241_, v_name_1242_, v_bi_boxed_1256_, v_type_1244_, v_k_1245_, v_kind_boxed_1257_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1258_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(lean_object* v_00_u03b1_1259_, lean_object* v_name_1260_, lean_object* v_type_1261_, lean_object* v_k_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_1260_, v_type_1261_, v_k_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1260_ = stack[1].m_obj;
lean_object* v_type_1261_ = stack[2].m_obj;
lean_object* v_k_1262_ = stack[3].m_obj;
lean_object* v___y_1263_ = stack[4].m_obj;
lean_object* v___y_1264_ = stack[5].m_obj;
lean_object* v___y_1265_ = stack[6].m_obj;
lean_object* v___y_1266_ = stack[7].m_obj;
lean_object* v___y_1267_ = stack[8].m_obj;
lean_object* v___y_1268_ = stack[9].m_obj;
lean_object* v___y_1269_ = stack[10].m_obj;
lean_object* v___y_1270_ = stack[11].m_obj;
lean_object* v_res_1273_;
v_res_1273_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(lean_box(0), v_name_1260_, v_type_1261_, v_k_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
stack->m_obj
 = v_res_1273_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_name_1275_, lean_object* v_type_1276_, lean_object* v_k_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(v_00_u03b1_1274_, v_name_1275_, v_type_1276_, v_k_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3(lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_x_1289_, v_x_1290_, v_x_1291_);
return v___x_1292_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1293_, lean_object* v_x_1294_, size_t v_x_1295_, size_t v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_1294_, v_x_1295_, v_x_1296_, v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1294_ = stack[1].m_obj;
size_t v_x_1295_ = stack[2].m_num;
size_t v_x_1296_ = stack[3].m_num;
lean_object* v_x_1297_ = stack[4].m_obj;
lean_object* v_x_1298_ = stack[5].m_obj;
lean_object* v_res_1300_;
v_res_1300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(lean_box(0), v_x_1294_, v_x_1295_, v_x_1296_, v_x_1297_, v_x_1298_);
stack->m_obj
 = v_res_1300_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
size_t v_x_11074__boxed_1307_; size_t v_x_11075__boxed_1308_; lean_object* v_res_1309_; 
v_x_11074__boxed_1307_ = lean_unbox_usize(v_x_1303_);
lean_dec(v_x_1303_);
v_x_11075__boxed_1308_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_res_1309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(v_00_u03b2_1301_, v_x_1302_, v_x_11074__boxed_1307_, v_x_11075__boxed_1308_, v_x_1305_, v_x_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_1310_, lean_object* v_n_1311_, lean_object* v_k_1312_, lean_object* v_v_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v_n_1311_, v_k_1312_, v_v_1313_);
return v___x_1314_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1315_, size_t v_depth_1316_, lean_object* v_keys_1317_, lean_object* v_vals_1318_, lean_object* v_heq_1319_, lean_object* v_i_1320_, lean_object* v_entries_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_1316_, v_keys_1317_, v_vals_1318_, v_i_1320_, v_entries_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1316_ = stack[1].m_num;
lean_object* v_keys_1317_ = stack[2].m_obj;
lean_object* v_vals_1318_ = stack[3].m_obj;
lean_object* v_i_1320_ = stack[5].m_obj;
lean_object* v_entries_1321_ = stack[6].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(lean_box(0), v_depth_1316_, v_keys_1317_, v_vals_1318_, lean_box(0), v_i_1320_, v_entries_1321_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_depth_1325_, lean_object* v_keys_1326_, lean_object* v_vals_1327_, lean_object* v_heq_1328_, lean_object* v_i_1329_, lean_object* v_entries_1330_){
_start:
{
size_t v_depth_boxed_1331_; lean_object* v_res_1332_; 
v_depth_boxed_1331_ = lean_unbox_usize(v_depth_1325_);
lean_dec(v_depth_1325_);
v_res_1332_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_1324_, v_depth_boxed_1331_, v_keys_1326_, v_vals_1327_, v_heq_1328_, v_i_1329_, v_entries_1330_);
lean_dec_ref(v_vals_1327_);
lean_dec_ref(v_keys_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_x_1334_, v_x_1335_, v_x_1336_, v_x_1337_);
return v___x_1338_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1(){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1350_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3));
v___x_1352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3));
v___x_1353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed), 10, 0);
v___x_1354_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1350_, v___x_1351_, v___x_1352_, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1355_;
v_res_1355_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0(lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v_00_u03c3s_1364_, lean_object* v_hyps_1365_, lean_object* v_target_1366_, lean_object* v_00_u03c6_1367_, lean_object* v_inst_1368_, lean_object* v_toPure_1369_, lean_object* v_____x_1370_){
_start:
{
lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1385_; 
v_fst_1371_ = lean_ctor_get(v_____x_1370_, 0);
v_snd_1372_ = lean_ctor_get(v_____x_1370_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_____x_1370_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1374_ = v_____x_1370_;
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_____x_1370_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_prf_1380_; lean_object* v___x_1382_; 
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0));
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0));
v___x_1378_ = l_Lean_Name_mkStr6(v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_, v___x_1376_, v___x_1377_);
v___x_1379_ = l_Lean_mkConst(v___x_1378_, v___x_1363_);
v_prf_1380_ = l_Lean_mkApp6(v___x_1379_, v_00_u03c3s_1364_, v_hyps_1365_, v_target_1366_, v_00_u03c6_1367_, v_inst_1368_, v_snd_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_prf_1380_);
v___x_1382_ = v___x_1374_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1371_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_prf_1380_);
v___x_1382_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_apply_2(v_toPure_1369_, lean_box(0), v___x_1382_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1(lean_object* v___x_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v_00_u03c3s_1391_, lean_object* v_hyps_1392_, lean_object* v_target_1393_, lean_object* v_00_u03c6_1394_, lean_object* v_toPure_1395_, lean_object* v_k_1396_, lean_object* v_toBind_1397_, lean_object* v_inst_1398_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v_00_u03c6_1394_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0), 12, 11);
lean_closure_set(v___f_1399_, 0, v___x_1386_);
lean_closure_set(v___f_1399_, 1, v___x_1387_);
lean_closure_set(v___f_1399_, 2, v___x_1388_);
lean_closure_set(v___f_1399_, 3, v___x_1389_);
lean_closure_set(v___f_1399_, 4, v___x_1390_);
lean_closure_set(v___f_1399_, 5, v_00_u03c3s_1391_);
lean_closure_set(v___f_1399_, 6, v_hyps_1392_);
lean_closure_set(v___f_1399_, 7, v_target_1393_);
lean_closure_set(v___f_1399_, 8, v_00_u03c6_1394_);
lean_closure_set(v___f_1399_, 9, v_inst_1398_);
lean_closure_set(v___f_1399_, 10, v_toPure_1395_);
v___x_1400_ = lean_apply_1(v_k_1396_, v_00_u03c6_1394_);
v___x_1401_ = lean_apply_4(v_toBind_1397_, lean_box(0), lean_box(0), v___x_1400_, v___f_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2(lean_object* v_goal_1402_, lean_object* v_toPure_1403_, lean_object* v_k_1404_, lean_object* v_toBind_1405_, lean_object* v_inst_1406_, lean_object* v_00_u03c6_1407_){
_start:
{
lean_object* v_u_1408_; lean_object* v_00_u03c3s_1409_; lean_object* v_hyps_1410_; lean_object* v_target_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_u_1408_ = lean_ctor_get(v_goal_1402_, 0);
lean_inc(v_u_1408_);
v_00_u03c3s_1409_ = lean_ctor_get(v_goal_1402_, 1);
lean_inc_ref_n(v_00_u03c3s_1409_, 2);
v_hyps_1410_ = lean_ctor_get(v_goal_1402_, 2);
lean_inc_ref(v_hyps_1410_);
v_target_1411_ = lean_ctor_get(v_goal_1402_, 3);
lean_inc_ref_n(v_target_1411_, 2);
lean_dec_ref(v_goal_1402_);
v___x_1412_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0));
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1));
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2));
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3));
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_u_1408_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
lean_inc(v_toBind_1405_);
lean_inc_ref(v_00_u03c6_1407_);
lean_inc_ref(v___x_1418_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1), 13, 12);
lean_closure_set(v___f_1419_, 0, v___x_1412_);
lean_closure_set(v___f_1419_, 1, v___x_1413_);
lean_closure_set(v___f_1419_, 2, v___x_1414_);
lean_closure_set(v___f_1419_, 3, v___x_1415_);
lean_closure_set(v___f_1419_, 4, v___x_1418_);
lean_closure_set(v___f_1419_, 5, v_00_u03c3s_1409_);
lean_closure_set(v___f_1419_, 6, v_hyps_1410_);
lean_closure_set(v___f_1419_, 7, v_target_1411_);
lean_closure_set(v___f_1419_, 8, v_00_u03c6_1407_);
lean_closure_set(v___f_1419_, 9, v_toPure_1403_);
lean_closure_set(v___f_1419_, 10, v_k_1404_);
lean_closure_set(v___f_1419_, 11, v_toBind_1405_);
v___x_1420_ = l_Lean_mkConst(v___x_1416_, v___x_1418_);
v___x_1421_ = l_Lean_mkApp3(v___x_1420_, v_00_u03c3s_1409_, v_target_1411_, v_00_u03c6_1407_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_closure((void*)(l_Lean_Meta_synthInstance___boxed), 7, 2);
lean_closure_set(v___x_1423_, 0, v___x_1421_);
lean_closure_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_apply_2(v_inst_1406_, lean_box(0), v___x_1423_);
v___x_1425_ = lean_apply_4(v_toBind_1405_, lean_box(0), lean_box(0), v___x_1424_, v___f_1419_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_goal_1428_, lean_object* v_k_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toBind_1431_; lean_object* v_toPure_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1426_, 0);
lean_inc_ref(v_toApplicative_1430_);
v_toBind_1431_ = lean_ctor_get(v_inst_1426_, 1);
lean_inc_n(v_toBind_1431_, 2);
lean_dec_ref(v_inst_1426_);
v_toPure_1432_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1432_);
lean_dec_ref(v_toApplicative_1430_);
v___x_1433_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2);
lean_inc(v_inst_1427_);
v___x_1434_ = lean_apply_2(v_inst_1427_, lean_box(0), v___x_1433_);
v___f_1435_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1435_, 0, v_goal_1428_);
lean_closure_set(v___f_1435_, 1, v_toPure_1432_);
lean_closure_set(v___f_1435_, 2, v_k_1429_);
lean_closure_set(v___f_1435_, 3, v_toBind_1431_);
lean_closure_set(v___f_1435_, 4, v_inst_1427_);
v___x_1436_ = lean_apply_4(v_toBind_1431_, lean_box(0), lean_box(0), v___x_1434_, v___f_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore(lean_object* v_m_1437_, lean_object* v_00_u03b1_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_goal_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(v_inst_1439_, v_inst_1440_, v_goal_1441_, v_k_1442_);
return v___x_1443_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(lean_object* v_goal_1451_, lean_object* v_k_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_1463_ = 0;
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Lean_Meta_mkFreshExprMVar(v___x_1462_, v___x_1463_, v___x_1464_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v_u_1467_; lean_object* v_00_u03c3s_1468_; lean_object* v_hyps_1469_; lean_object* v_target_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc_n(v_a_1466_, 2);
lean_dec_ref_known(v___x_1465_, 1);
v_u_1467_ = lean_ctor_get(v_goal_1451_, 0);
lean_inc(v_u_1467_);
v_00_u03c3s_1468_ = lean_ctor_get(v_goal_1451_, 1);
lean_inc_ref_n(v_00_u03c3s_1468_, 2);
v_hyps_1469_ = lean_ctor_get(v_goal_1451_, 2);
lean_inc_ref(v_hyps_1469_);
v_target_1470_ = lean_ctor_get(v_goal_1451_, 3);
lean_inc_ref_n(v_target_1470_, 2);
lean_dec_ref(v_goal_1451_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_u_1467_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
lean_inc_ref(v___x_1473_);
v___x_1474_ = l_Lean_mkConst(v___x_1471_, v___x_1473_);
v___x_1475_ = l_Lean_mkApp3(v___x_1474_, v_00_u03c3s_1468_, v_target_1470_, v_a_1466_);
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_Meta_synthInstance(v___x_1475_, v___x_1476_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v_a_1466_);
v___x_1479_ = lean_apply_10(v_k_1452_, v_a_1466_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, lean_box(0));
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1499_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1498_; 
v_fst_1484_ = lean_ctor_get(v_a_1480_, 0);
v_snd_1485_ = lean_ctor_get(v_a_1480_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1480_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1487_ = v_a_1480_;
v_isShared_1488_ = v_isSharedCheck_1498_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_snd_1485_);
lean_inc(v_fst_1484_);
lean_dec(v_a_1480_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1498_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_prf_1491_; lean_object* v___x_1493_; 
v___x_1489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0));
v___x_1490_ = l_Lean_mkConst(v___x_1489_, v___x_1473_);
v_prf_1491_ = l_Lean_mkApp6(v___x_1490_, v_00_u03c3s_1468_, v_hyps_1469_, v_target_1470_, v_a_1466_, v_a_1478_, v_snd_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_prf_1491_);
v___x_1493_ = v___x_1487_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_fst_1484_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_prf_1491_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1493_);
v___x_1495_ = v___x_1482_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_dec(v_a_1478_);
lean_dec_ref_known(v___x_1473_, 2);
lean_dec_ref(v_target_1470_);
lean_dec_ref(v_hyps_1469_);
lean_dec_ref(v_00_u03c3s_1468_);
lean_dec(v_a_1466_);
return v___x_1479_;
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref_known(v___x_1473_, 2);
lean_dec_ref(v_target_1470_);
lean_dec_ref(v_hyps_1469_);
lean_dec_ref(v_00_u03c3s_1468_);
lean_dec(v_a_1466_);
lean_dec_ref(v_k_1452_);
v_a_1500_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1477_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1477_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_k_1452_);
lean_dec_ref(v_goal_1451_);
v_a_1508_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1465_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1465_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1451_ = stack[0].m_obj;
lean_object* v_k_1452_ = stack[1].m_obj;
lean_object* v___y_1453_ = stack[2].m_obj;
lean_object* v___y_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v___y_1456_ = stack[5].m_obj;
lean_object* v___y_1457_ = stack[6].m_obj;
lean_object* v___y_1458_ = stack[7].m_obj;
lean_object* v___y_1459_ = stack[8].m_obj;
lean_object* v___y_1460_ = stack[9].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_1451_, v_k_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___boxed(lean_object* v_goal_1517_, lean_object* v_k_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_1517_, v_k_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1528_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(lean_object* v_00_u03b1_1529_, lean_object* v_goal_1530_, lean_object* v_k_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_1530_, v_k_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1530_ = stack[1].m_obj;
lean_object* v_k_1531_ = stack[2].m_obj;
lean_object* v___y_1532_ = stack[3].m_obj;
lean_object* v___y_1533_ = stack[4].m_obj;
lean_object* v___y_1534_ = stack[5].m_obj;
lean_object* v___y_1535_ = stack[6].m_obj;
lean_object* v___y_1536_ = stack[7].m_obj;
lean_object* v___y_1537_ = stack[8].m_obj;
lean_object* v___y_1538_ = stack[9].m_obj;
lean_object* v___y_1539_ = stack[10].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(lean_box(0), v_goal_1530_, v_k_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_goal_1544_, lean_object* v_k_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(v_00_u03b1_1543_, v_goal_1544_, v_k_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1555_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(lean_object* v_fst_1556_, lean_object* v_00_u03c6_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_MVarId_getTag(v_fst_1556_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_00_u03c6_1557_, v_a_1568_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = l_Lean_Expr_mvarId_x21(v_a_1570_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1569_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1569_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_00_u03c6_1557_);
v_a_1588_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1567_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1567_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1556_ = stack[0].m_obj;
lean_object* v_00_u03c6_1557_ = stack[1].m_obj;
lean_object* v___y_1558_ = stack[2].m_obj;
lean_object* v___y_1559_ = stack[3].m_obj;
lean_object* v___y_1560_ = stack[4].m_obj;
lean_object* v___y_1561_ = stack[5].m_obj;
lean_object* v___y_1562_ = stack[6].m_obj;
lean_object* v___y_1563_ = stack[7].m_obj;
lean_object* v___y_1564_ = stack[8].m_obj;
lean_object* v___y_1565_ = stack[9].m_obj;
lean_object* v_res_1596_;
v_res_1596_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(v_fst_1556_, v_00_u03c6_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
stack->m_obj
 = v_res_1596_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed(lean_object* v_fst_1597_, lean_object* v_00_u03c6_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(v_fst_1597_, v_00_u03c6_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1608_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(lean_object* v_snd_1609_, lean_object* v___f_1610_, lean_object* v_fst_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_snd_1609_, v___f_1610_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1634_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_fst_1623_ = lean_ctor_get(v_a_1622_, 0);
v_snd_1624_ = lean_ctor_get(v_a_1622_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1622_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1626_ = v_a_1622_;
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_inc(v_fst_1623_);
lean_dec(v_a_1622_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1628_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_1611_, v_snd_1624_, v___y_1617_);
lean_dec_ref(v___x_1628_);
v___x_1629_ = lean_box(0);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
lean_ctor_set(v___x_1626_, 1, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fst_1623_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1631_, v___y_1613_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_fst_1611_);
v_a_1635_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1621_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1621_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1609_ = stack[0].m_obj;
lean_object* v___f_1610_ = stack[1].m_obj;
lean_object* v_fst_1611_ = stack[2].m_obj;
lean_object* v___y_1612_ = stack[3].m_obj;
lean_object* v___y_1613_ = stack[4].m_obj;
lean_object* v___y_1614_ = stack[5].m_obj;
lean_object* v___y_1615_ = stack[6].m_obj;
lean_object* v___y_1616_ = stack[7].m_obj;
lean_object* v___y_1617_ = stack[8].m_obj;
lean_object* v___y_1618_ = stack[9].m_obj;
lean_object* v___y_1619_ = stack[10].m_obj;
lean_object* v_res_1643_;
v_res_1643_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(v_snd_1609_, v___f_1610_, v_fst_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
stack->m_obj
 = v_res_1643_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed(lean_object* v_snd_1644_, lean_object* v___f_1645_, lean_object* v_fst_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(v_snd_1644_, v___f_1645_, v_fst_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1656_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(lean_object* v_x_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1));
v___x_1674_ = l_Lean_Syntax_isOfKind(v_x_1663_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1665_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v_fst_1678_ = lean_ctor_get(v_a_1677_, 0);
lean_inc_n(v_fst_1678_, 3);
v_snd_1679_ = lean_ctor_get(v_a_1677_, 1);
lean_inc(v_snd_1679_);
lean_dec(v_a_1677_);
v___f_1680_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1680_, 0, v_fst_1678_);
v___f_1681_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1681_, 0, v_snd_1679_);
lean_closure_set(v___f_1681_, 1, v___f_1680_);
lean_closure_set(v___f_1681_, 2, v_fst_1678_);
v___x_1682_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_1678_, v___f_1681_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
return v___x_1682_;
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1676_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1676_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1663_ = stack[0].m_obj;
lean_object* v_a_1664_ = stack[1].m_obj;
lean_object* v_a_1665_ = stack[2].m_obj;
lean_object* v_a_1666_ = stack[3].m_obj;
lean_object* v_a_1667_ = stack[4].m_obj;
lean_object* v_a_1668_ = stack[5].m_obj;
lean_object* v_a_1669_ = stack[6].m_obj;
lean_object* v_a_1670_ = stack[7].m_obj;
lean_object* v_a_1671_ = stack[8].m_obj;
lean_object* v_res_1691_;
v_res_1691_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(v_x_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
stack->m_obj
 = v_res_1691_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed(lean_object* v_x_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(v_x_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1702_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1(){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1712_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1));
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1));
v___x_1715_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed), 10, 0);
v___x_1716_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1712_, v___x_1713_, v___x_1714_, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1717_;
v_res_1717_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___boxed(lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
return v_res_1719_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5(void){
_start:
{
lean_object* v___x_1731_; lean_object* v_dummy_1732_; 
v___x_1731_ = lean_box(0);
v_dummy_1732_ = l_Lean_Expr_sort___override(v___x_1731_);
return v_dummy_1732_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(lean_object* v_e_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = l_Lean_instInhabitedExpr;
v___x_1740_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1733_, v_a_1735_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1799_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1799_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1799_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2));
v___x_1746_ = lean_unsigned_to_nat(2u);
v___x_1747_ = l_Lean_Expr_isAppOfArity(v_a_1741_, v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
lean_dec(v_a_1741_);
v___x_1748_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1748_);
v___x_1750_ = v___x_1743_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1752_ = l_Lean_Expr_appArg_x21(v_a_1741_);
lean_dec(v_a_1741_);
v___x_1753_ = l_Lean_Expr_getAppFn(v___x_1752_);
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4));
v___x_1755_ = l_Lean_Expr_isConstOf(v___x_1753_, v___x_1754_);
lean_dec_ref(v___x_1753_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec_ref(v___x_1752_);
v___x_1756_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1756_);
v___x_1758_ = v___x_1743_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
else
{
lean_object* v_dummy_1760_; lean_object* v_nargs_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_dummy_1760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5, &l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5);
v_nargs_1761_ = l_Lean_Expr_getAppNumArgs(v___x_1752_);
lean_inc(v_nargs_1761_);
v___x_1762_ = lean_mk_array(v_nargs_1761_, v_dummy_1760_);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_sub(v_nargs_1761_, v___x_1763_);
lean_dec(v_nargs_1761_);
v___x_1765_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1752_, v___x_1762_, v___x_1764_);
v___x_1766_ = lean_array_get_size(v___x_1765_);
v___x_1767_ = lean_nat_dec_lt(v___x_1766_, v___x_1746_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_del_object(v___x_1743_);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_array_get_borrowed(v___x_1739_, v___x_1765_, v___x_1768_);
lean_inc(v___x_1769_);
v___x_1770_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(v___x_1769_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1786_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1786_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_nat_sub(v___x_1766_, v___x_1746_);
v___x_1776_ = lean_nat_dec_eq(v_a_1771_, v___x_1775_);
lean_dec(v___x_1775_);
lean_dec(v_a_1771_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec_ref(v___x_1765_);
v___x_1777_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1777_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = lean_array_get(v___x_1739_, v___x_1765_, v___x_1763_);
lean_dec_ref(v___x_1765_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1782_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___x_1765_);
v_a_1787_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1770_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1770_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_dec_ref(v___x_1765_);
v___x_1795_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1795_);
v___x_1797_ = v___x_1743_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1740_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1740_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1733_ = stack[0].m_obj;
lean_object* v_a_1734_ = stack[1].m_obj;
lean_object* v_a_1735_ = stack[2].m_obj;
lean_object* v_a_1736_ = stack[3].m_obj;
lean_object* v_a_1737_ = stack[4].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_e_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___boxed(lean_object* v_e_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_e_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1815_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(lean_object* v_msgData_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v_env_1823_; uint8_t v___x_1824_; lean_object* v_env_1825_; lean_object* v___x_1826_; lean_object* v_toCold_1827_; lean_object* v_mctx_1828_; lean_object* v_lctx_1829_; lean_object* v_options_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1822_ = lean_st_ref_get(v___y_1820_);
v_env_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc_ref(v_env_1823_);
lean_dec(v___x_1822_);
v___x_1824_ = 0;
v_env_1825_ = l_Lean_Environment_setRecordingDeps(v_env_1823_, v___x_1824_);
v___x_1826_ = lean_st_ref_get(v___y_1818_);
v_toCold_1827_ = lean_ctor_get(v___y_1819_, 0);
v_mctx_1828_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_ref(v_mctx_1828_);
lean_dec(v___x_1826_);
v_lctx_1829_ = lean_ctor_get(v___y_1817_, 2);
v_options_1830_ = lean_ctor_get(v_toCold_1827_, 2);
lean_inc_ref(v_options_1830_);
lean_inc_ref(v_lctx_1829_);
v___x_1831_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1831_, 0, v_env_1825_);
lean_ctor_set(v___x_1831_, 1, v_mctx_1828_);
lean_ctor_set(v___x_1831_, 2, v_lctx_1829_);
lean_ctor_set(v___x_1831_, 3, v_options_1830_);
v___x_1832_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v_msgData_1816_);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1816_ = stack[0].m_obj;
lean_object* v___y_1817_ = stack[1].m_obj;
lean_object* v___y_1818_ = stack[2].m_obj;
lean_object* v___y_1819_ = stack[3].m_obj;
lean_object* v___y_1820_ = stack[4].m_obj;
lean_object* v_res_1834_;
v_res_1834_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msgData_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
stack->m_obj
 = v_res_1834_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1___boxed(lean_object* v_msgData_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msgData_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1842_; double v___x_1843_; 
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_float_of_nat(v___x_1842_);
return v___x_1843_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(lean_object* v_cls_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_ref_1854_; lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1901_; 
v_ref_1854_ = lean_ctor_get(v___y_1851_, 2);
v___x_1855_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1901_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1901_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v_traceState_1861_; lean_object* v_env_1862_; lean_object* v_nextMacroScope_1863_; lean_object* v_ngen_1864_; lean_object* v_auxDeclNGen_1865_; lean_object* v_cache_1866_; lean_object* v_recordedDeps_1867_; lean_object* v_messages_1868_; lean_object* v_infoState_1869_; lean_object* v_snapshotTasks_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1900_; 
v___x_1860_ = lean_st_ref_take(v___y_1852_);
v_traceState_1861_ = lean_ctor_get(v___x_1860_, 4);
v_env_1862_ = lean_ctor_get(v___x_1860_, 0);
v_nextMacroScope_1863_ = lean_ctor_get(v___x_1860_, 1);
v_ngen_1864_ = lean_ctor_get(v___x_1860_, 2);
v_auxDeclNGen_1865_ = lean_ctor_get(v___x_1860_, 3);
v_cache_1866_ = lean_ctor_get(v___x_1860_, 5);
v_recordedDeps_1867_ = lean_ctor_get(v___x_1860_, 6);
v_messages_1868_ = lean_ctor_get(v___x_1860_, 7);
v_infoState_1869_ = lean_ctor_get(v___x_1860_, 8);
v_snapshotTasks_1870_ = lean_ctor_get(v___x_1860_, 9);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1872_ = v___x_1860_;
v_isShared_1873_ = v_isSharedCheck_1900_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_snapshotTasks_1870_);
lean_inc(v_infoState_1869_);
lean_inc(v_messages_1868_);
lean_inc(v_recordedDeps_1867_);
lean_inc(v_cache_1866_);
lean_inc(v_traceState_1861_);
lean_inc(v_auxDeclNGen_1865_);
lean_inc(v_ngen_1864_);
lean_inc(v_nextMacroScope_1863_);
lean_inc(v_env_1862_);
lean_dec(v___x_1860_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1900_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
uint64_t v_tid_1874_; lean_object* v_traces_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1899_; 
v_tid_1874_ = lean_ctor_get_uint64(v_traceState_1861_, sizeof(void*)*1);
v_traces_1875_ = lean_ctor_get(v_traceState_1861_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_traceState_1861_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1877_ = v_traceState_1861_;
v_isShared_1878_ = v_isSharedCheck_1899_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_traces_1875_);
lean_dec(v_traceState_1861_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1899_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; double v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_float_once(&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
v___x_1882_ = 0;
v___x_1883_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1));
v___x_1884_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1884_, 0, v_cls_1847_);
lean_ctor_set(v___x_1884_, 1, v___x_1880_);
lean_ctor_set(v___x_1884_, 2, v___x_1883_);
lean_ctor_set_float(v___x_1884_, sizeof(void*)*3, v___x_1881_);
lean_ctor_set_float(v___x_1884_, sizeof(void*)*3 + 8, v___x_1881_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*3 + 16, v___x_1882_);
v___x_1885_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2));
v___x_1886_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v_a_1856_);
lean_ctor_set(v___x_1886_, 2, v___x_1885_);
lean_inc(v_ref_1854_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v_ref_1854_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_PersistentArray_push___redArg(v_traces_1875_, v___x_1887_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1888_);
v___x_1890_ = v___x_1877_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1888_);
lean_ctor_set_uint64(v_reuseFailAlloc_1898_, sizeof(void*)*1, v_tid_1874_);
v___x_1890_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___x_1890_);
v___x_1892_ = v___x_1872_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_env_1862_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_nextMacroScope_1863_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_ngen_1864_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_auxDeclNGen_1865_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1897_, 5, v_cache_1866_);
lean_ctor_set(v_reuseFailAlloc_1897_, 6, v_recordedDeps_1867_);
lean_ctor_set(v_reuseFailAlloc_1897_, 7, v_messages_1868_);
lean_ctor_set(v_reuseFailAlloc_1897_, 8, v_infoState_1869_);
lean_ctor_set(v_reuseFailAlloc_1897_, 9, v_snapshotTasks_1870_);
v___x_1892_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_st_ref_put(v___y_1852_, v___x_1892_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1879_);
v___x_1895_ = v___x_1858_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1879_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1847_ = stack[0].m_obj;
lean_object* v_msg_1848_ = stack[1].m_obj;
lean_object* v___y_1849_ = stack[2].m_obj;
lean_object* v___y_1850_ = stack[3].m_obj;
lean_object* v___y_1851_ = stack[4].m_obj;
lean_object* v___y_1852_ = stack[5].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(v_cls_1847_, v_msg_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___boxed(lean_object* v_cls_1903_, lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(v_cls_1903_, v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1910_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(lean_object* v_mvarId_1911_, lean_object* v_val_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_mctx_1916_; lean_object* v_cache_1917_; lean_object* v_zetaDeltaFVarIds_1918_; lean_object* v_postponed_1919_; lean_object* v_diag_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1950_; 
v___x_1915_ = lean_st_ref_take(v___y_1913_);
v_mctx_1916_ = lean_ctor_get(v___x_1915_, 0);
v_cache_1917_ = lean_ctor_get(v___x_1915_, 1);
v_zetaDeltaFVarIds_1918_ = lean_ctor_get(v___x_1915_, 2);
v_postponed_1919_ = lean_ctor_get(v___x_1915_, 3);
v_diag_1920_ = lean_ctor_get(v___x_1915_, 4);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1922_ = v___x_1915_;
v_isShared_1923_ = v_isSharedCheck_1950_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_diag_1920_);
lean_inc(v_postponed_1919_);
lean_inc(v_zetaDeltaFVarIds_1918_);
lean_inc(v_cache_1917_);
lean_inc(v_mctx_1916_);
lean_dec(v___x_1915_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1950_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_depth_1924_; lean_object* v_levelAssignDepth_1925_; lean_object* v_lmvarCounter_1926_; lean_object* v_mvarCounter_1927_; lean_object* v_lDecls_1928_; lean_object* v_decls_1929_; lean_object* v_userNames_1930_; lean_object* v_lAssignment_1931_; lean_object* v_eAssignment_1932_; lean_object* v_dAssignment_1933_; lean_object* v_instanceTypedMVars_1934_; lean_object* v_synthNormMemo_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1949_; 
v_depth_1924_ = lean_ctor_get(v_mctx_1916_, 0);
v_levelAssignDepth_1925_ = lean_ctor_get(v_mctx_1916_, 1);
v_lmvarCounter_1926_ = lean_ctor_get(v_mctx_1916_, 2);
v_mvarCounter_1927_ = lean_ctor_get(v_mctx_1916_, 3);
v_lDecls_1928_ = lean_ctor_get(v_mctx_1916_, 4);
v_decls_1929_ = lean_ctor_get(v_mctx_1916_, 5);
v_userNames_1930_ = lean_ctor_get(v_mctx_1916_, 6);
v_lAssignment_1931_ = lean_ctor_get(v_mctx_1916_, 7);
v_eAssignment_1932_ = lean_ctor_get(v_mctx_1916_, 8);
v_dAssignment_1933_ = lean_ctor_get(v_mctx_1916_, 9);
v_instanceTypedMVars_1934_ = lean_ctor_get(v_mctx_1916_, 10);
v_synthNormMemo_1935_ = lean_ctor_get(v_mctx_1916_, 11);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_mctx_1916_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1937_ = v_mctx_1916_;
v_isShared_1938_ = v_isSharedCheck_1949_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_synthNormMemo_1935_);
lean_inc(v_instanceTypedMVars_1934_);
lean_inc(v_dAssignment_1933_);
lean_inc(v_eAssignment_1932_);
lean_inc(v_lAssignment_1931_);
lean_inc(v_userNames_1930_);
lean_inc(v_decls_1929_);
lean_inc(v_lDecls_1928_);
lean_inc(v_mvarCounter_1927_);
lean_inc(v_lmvarCounter_1926_);
lean_inc(v_levelAssignDepth_1925_);
lean_inc(v_depth_1924_);
lean_dec(v_mctx_1916_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1949_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_1932_, v_mvarId_1911_, v_val_1912_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 8, v___x_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_depth_1924_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_levelAssignDepth_1925_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_lmvarCounter_1926_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_mvarCounter_1927_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_lDecls_1928_);
lean_ctor_set(v_reuseFailAlloc_1948_, 5, v_decls_1929_);
lean_ctor_set(v_reuseFailAlloc_1948_, 6, v_userNames_1930_);
lean_ctor_set(v_reuseFailAlloc_1948_, 7, v_lAssignment_1931_);
lean_ctor_set(v_reuseFailAlloc_1948_, 8, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 9, v_dAssignment_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 10, v_instanceTypedMVars_1934_);
lean_ctor_set(v_reuseFailAlloc_1948_, 11, v_synthNormMemo_1935_);
v___x_1942_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1942_);
v___x_1944_ = v___x_1922_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_cache_1917_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_zetaDeltaFVarIds_1918_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_postponed_1919_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_diag_1920_);
v___x_1944_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_st_ref_put(v___y_1913_, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1939_);
return v___x_1946_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1911_ = stack[0].m_obj;
lean_object* v_val_1912_ = stack[1].m_obj;
lean_object* v___y_1913_ = stack[2].m_obj;
lean_object* v_res_1951_;
v_res_1951_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvarId_1911_, v_val_1912_, v___y_1913_);
stack->m_obj
 = v_res_1951_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg___boxed(lean_object* v_mvarId_1952_, lean_object* v_val_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvarId_1952_, v_val_1953_, v___y_1954_);
lean_dec(v___y_1954_);
return v_res_1956_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_box(0);
v___x_1967_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__4));
v___x_1968_ = l_Lean_mkConst(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__6));
v___x_1974_ = l_Lean_mkConst(v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___x_1985_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
v___x_1986_ = l_Lean_Name_append(v___x_1985_, v___x_1984_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__13));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
lean_object* l_Lean_MVarId_applyRflAndAndIntro(lean_object* v_mvar_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v_a_2046_; lean_object* v___y_2059_; lean_object* v___x_2080_; 
lean_inc(v_mvar_1990_);
v___x_2080_ = l_Lean_MVarId_getType(v_mvar_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v___x_2082_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2081_, v_a_1992_);
v___y_2059_ = v___x_2082_;
goto v___jp_2058_;
}
else
{
v___y_2059_ = v___x_2080_;
goto v___jp_2058_;
}
v___jp_1996_:
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__1));
v___x_2003_ = l_Lean_Expr_isAppOf(v___y_1997_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__3));
v___x_2005_ = lean_unsigned_to_nat(2u);
v___x_2006_ = l_Lean_Expr_isAppOfArity(v___y_1997_, v___x_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_inc(v_mvar_1990_);
v___x_2007_ = l_Lean_MVarId_setType___redArg(v_mvar_1990_, v___y_1997_, v___y_1999_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
lean_dec_ref_known(v___x_2007_, 1);
v___x_2008_ = l_Lean_MVarId_applyRfl(v_mvar_1990_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2008_;
}
else
{
lean_dec(v_mvar_1990_);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2009_ = l_Lean_Expr_appFn_x21(v___y_1997_);
v___x_2010_ = l_Lean_Expr_appArg_x21(v___x_2009_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = l_Lean_Expr_appArg_x21(v___y_1997_);
lean_dec_ref(v___y_1997_);
lean_inc_ref(v___x_2010_);
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2010_);
v___x_2013_ = 0;
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Meta_mkFreshExprMVar(v___x_2012_, v___x_2013_, v___x_2014_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
lean_inc_ref(v___x_2011_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
v___x_2018_ = l_Lean_Meta_mkFreshExprMVar(v___x_2017_, v___x_2013_, v___x_2014_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = l_Lean_Expr_mvarId_x21(v_a_2016_);
v___x_2021_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2020_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref_known(v___x_2021_, 1);
v___x_2022_ = l_Lean_Expr_mvarId_x21(v_a_2019_);
v___x_2023_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2022_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec_ref_known(v___x_2023_, 1);
v___x_2024_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__5, &l_Lean_MVarId_applyRflAndAndIntro___closed__5_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5);
v___x_2025_ = l_Lean_mkApp4(v___x_2024_, v___x_2010_, v___x_2011_, v_a_2016_, v_a_2019_);
v___x_2026_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_1990_, v___x_2025_, v___y_1999_);
return v___x_2026_;
}
else
{
lean_dec(v_a_2019_);
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v___x_2010_);
lean_dec(v_mvar_1990_);
return v___x_2023_;
}
}
else
{
lean_dec(v_a_2019_);
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v___x_2010_);
lean_dec(v_mvar_1990_);
return v___x_2021_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v___x_2010_);
lean_dec(v_mvar_1990_);
v_a_2027_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2018_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2018_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v___x_2011_);
lean_dec_ref(v___x_2010_);
lean_dec(v_mvar_1990_);
v_a_2035_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2015_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2015_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___y_1997_);
v___x_2043_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__7, &l_Lean_MVarId_applyRflAndAndIntro___closed__7_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7);
v___x_2044_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_1990_, v___x_2043_, v___y_1999_);
return v___x_2044_;
}
}
v___jp_2045_:
{
lean_object* v_toCold_2047_; lean_object* v_options_2048_; uint8_t v_hasTrace_2049_; 
v_toCold_2047_ = lean_ctor_get(v_a_1993_, 0);
v_options_2048_ = lean_ctor_get(v_toCold_2047_, 2);
v_hasTrace_2049_ = lean_ctor_get_uint8(v_options_2048_, sizeof(void*)*1);
if (v_hasTrace_2049_ == 0)
{
v___y_1997_ = v_a_2046_;
v___y_1998_ = v_a_1991_;
v___y_1999_ = v_a_1992_;
v___y_2000_ = v_a_1993_;
v___y_2001_ = v_a_1994_;
goto v___jp_1996_;
}
else
{
lean_object* v_inheritedTraceOptions_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_inheritedTraceOptions_2050_ = lean_ctor_get(v_toCold_2047_, 11);
v___x_2051_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___x_2052_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__12, &l_Lean_MVarId_applyRflAndAndIntro___closed__12_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12);
v___x_2053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2050_, v_options_2048_, v___x_2052_);
if (v___x_2053_ == 0)
{
v___y_1997_ = v_a_2046_;
v___y_1998_ = v_a_1991_;
v___y_1999_ = v_a_1992_;
v___y_2000_ = v_a_1993_;
v___y_2001_ = v_a_1994_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = lean_obj_once(&l_Lean_MVarId_applyRflAndAndIntro___closed__14, &l_Lean_MVarId_applyRflAndAndIntro___closed__14_once, _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14);
lean_inc_ref(v_a_2046_);
v___x_2055_ = l_Lean_MessageData_ofExpr(v_a_2046_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(v___x_2051_, v___x_2056_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
v___y_1997_ = v_a_2046_;
v___y_1998_ = v_a_1991_;
v___y_1999_ = v_a_1992_;
v___y_2000_ = v_a_1993_;
v___y_2001_ = v_a_1994_;
goto v___jp_1996_;
}
else
{
lean_dec_ref(v_a_2046_);
lean_dec(v_mvar_1990_);
return v___x_2057_;
}
}
}
}
v___jp_2058_:
{
if (lean_obj_tag(v___y_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2061_; 
v_a_2060_ = lean_ctor_get(v___y_2059_, 0);
lean_inc_n(v_a_2060_, 2);
lean_dec_ref_known(v___y_2059_, 1);
v___x_2061_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_a_2060_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
if (lean_obj_tag(v_a_2062_) == 0)
{
v_a_2046_ = v_a_2060_;
goto v___jp_2045_;
}
else
{
lean_object* v_val_2063_; 
lean_dec(v_a_2060_);
v_val_2063_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v_a_2062_, 1);
v_a_2046_ = v_val_2063_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2060_);
lean_dec(v_mvar_1990_);
v_a_2064_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2061_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2061_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_mvar_1990_);
v_a_2072_ = lean_ctor_get(v___y_2059_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___y_2059_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___y_2059_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___y_2059_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_applyRflAndAndIntro_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_1990_ = stack[0].m_obj;
lean_object* v_a_1991_ = stack[1].m_obj;
lean_object* v_a_1992_ = stack[2].m_obj;
lean_object* v_a_1993_ = stack[3].m_obj;
lean_object* v_a_1994_ = stack[4].m_obj;
lean_object* v_res_2083_;
v_res_2083_ = l_Lean_MVarId_applyRflAndAndIntro(v_mvar_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
stack->m_obj
 = v_res_2083_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRflAndAndIntro___boxed(lean_object* v_mvar_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_MVarId_applyRflAndAndIntro(v_mvar_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2090_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(lean_object* v_mvarId_2091_, lean_object* v_val_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvarId_2091_, v_val_2092_, v___y_2094_);
return v___x_2098_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2091_ = stack[0].m_obj;
lean_object* v_val_2092_ = stack[1].m_obj;
lean_object* v___y_2093_ = stack[2].m_obj;
lean_object* v___y_2094_ = stack[3].m_obj;
lean_object* v___y_2095_ = stack[4].m_obj;
lean_object* v___y_2096_ = stack[5].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(v_mvarId_2091_, v_val_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___boxed(lean_object* v_mvarId_2100_, lean_object* v_val_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(v_mvarId_2100_, v_val_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2107_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(lean_object* v_goal_2108_, lean_object* v_k_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
v___x_2116_ = 0;
v___x_2117_ = lean_box(0);
v___x_2118_ = l_Lean_Meta_mkFreshExprMVar(v___x_2115_, v___x_2116_, v___x_2117_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_u_2120_; lean_object* v_00_u03c3s_2121_; lean_object* v_hyps_2122_; lean_object* v_target_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_n(v_a_2119_, 2);
lean_dec_ref_known(v___x_2118_, 1);
v_u_2120_ = lean_ctor_get(v_goal_2108_, 0);
lean_inc(v_u_2120_);
v_00_u03c3s_2121_ = lean_ctor_get(v_goal_2108_, 1);
lean_inc_ref_n(v_00_u03c3s_2121_, 2);
v_hyps_2122_ = lean_ctor_get(v_goal_2108_, 2);
lean_inc_ref(v_hyps_2122_);
v_target_2123_ = lean_ctor_get(v_goal_2108_, 3);
lean_inc_ref_n(v_target_2123_, 2);
lean_dec_ref(v_goal_2108_);
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5));
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_u_2120_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
lean_inc_ref(v___x_2126_);
v___x_2127_ = l_Lean_mkConst(v___x_2124_, v___x_2126_);
v___x_2128_ = l_Lean_mkApp3(v___x_2127_, v_00_u03c3s_2121_, v_target_2123_, v_a_2119_);
v___x_2129_ = lean_box(0);
v___x_2130_ = l_Lean_Meta_synthInstance(v___x_2128_, v___x_2129_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
lean_inc(v_a_2119_);
v___x_2132_ = lean_apply_6(v_k_2109_, v_a_2119_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, lean_box(0));
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
if (lean_obj_tag(v_a_2133_) == 0)
{
lean_dec(v_a_2131_);
lean_dec_ref_known(v___x_2126_, 2);
lean_dec_ref(v_target_2123_);
lean_dec_ref(v_hyps_2122_);
lean_dec_ref(v_00_u03c3s_2121_);
lean_dec(v_a_2119_);
return v___x_2132_;
}
else
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2132_, 0);
lean_dec(v_unused_2161_);
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2160_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_val_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2159_; 
v_val_2137_ = lean_ctor_get(v_a_2133_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2139_ = v_a_2133_;
v_isShared_2140_ = v_isSharedCheck_2159_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_val_2137_);
lean_dec(v_a_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2159_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2158_; 
v_fst_2141_ = lean_ctor_get(v_val_2137_, 0);
v_snd_2142_ = lean_ctor_get(v_val_2137_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_val_2137_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2144_ = v_val_2137_;
v_isShared_2145_ = v_isSharedCheck_2158_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_snd_2142_);
lean_inc(v_fst_2141_);
lean_dec(v_val_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2158_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_prf_2148_; lean_object* v___x_2150_; 
v___x_2146_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0));
v___x_2147_ = l_Lean_mkConst(v___x_2146_, v___x_2126_);
v_prf_2148_ = l_Lean_mkApp6(v___x_2147_, v_00_u03c3s_2121_, v_hyps_2122_, v_target_2123_, v_a_2119_, v_a_2131_, v_snd_2142_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v_prf_2148_);
v___x_2150_ = v___x_2144_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_fst_2141_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_prf_2148_);
v___x_2150_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2150_);
v___x_2152_ = v___x_2139_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2152_);
v___x_2154_ = v___x_2135_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
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
lean_dec(v_a_2131_);
lean_dec_ref_known(v___x_2126_, 2);
lean_dec_ref(v_target_2123_);
lean_dec_ref(v_hyps_2122_);
lean_dec_ref(v_00_u03c3s_2121_);
lean_dec(v_a_2119_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref_known(v___x_2126_, 2);
lean_dec_ref(v_target_2123_);
lean_dec_ref(v_hyps_2122_);
lean_dec_ref(v_00_u03c3s_2121_);
lean_dec(v_a_2119_);
lean_dec_ref(v_k_2109_);
v_a_2162_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2130_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2130_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_k_2109_);
lean_dec_ref(v_goal_2108_);
v_a_2170_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2118_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2118_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2108_ = stack[0].m_obj;
lean_object* v_k_2109_ = stack[1].m_obj;
lean_object* v___y_2110_ = stack[2].m_obj;
lean_object* v___y_2111_ = stack[3].m_obj;
lean_object* v___y_2112_ = stack[4].m_obj;
lean_object* v___y_2113_ = stack[5].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2108_, v_k_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg___boxed(lean_object* v_goal_2179_, lean_object* v_k_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2179_, v_k_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2186_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(lean_object* v_00_u03b1_2187_, lean_object* v_goal_2188_, lean_object* v_k_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2188_, v_k_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2188_ = stack[1].m_obj;
lean_object* v_k_2189_ = stack[2].m_obj;
lean_object* v___y_2190_ = stack[3].m_obj;
lean_object* v___y_2191_ = stack[4].m_obj;
lean_object* v___y_2192_ = stack[5].m_obj;
lean_object* v___y_2193_ = stack[6].m_obj;
lean_object* v_res_2196_;
v_res_2196_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(lean_box(0), v_goal_2188_, v_k_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
stack->m_obj
 = v_res_2196_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_goal_2198_, lean_object* v_k_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(v_00_u03b1_2197_, v_goal_2198_, v_k_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2205_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(lean_object* v_cls_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_toCold_2212_; lean_object* v_options_2213_; uint8_t v_hasTrace_2214_; 
v_toCold_2212_ = lean_ctor_get(v___y_2209_, 0);
v_options_2213_ = lean_ctor_get(v_toCold_2212_, 2);
v_hasTrace_2214_ = lean_ctor_get_uint8(v_options_2213_, sizeof(void*)*1);
if (v_hasTrace_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_cls_2206_);
v___x_2215_ = lean_box(v_hasTrace_2214_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
else
{
lean_object* v_inheritedTraceOptions_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_inheritedTraceOptions_2218_ = lean_ctor_get(v_toCold_2212_, 11);
v___x_2219_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
v___x_2220_ = l_Lean_Name_append(v___x_2219_, v_cls_2206_);
v___x_2221_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2218_, v_options_2213_, v___x_2220_);
lean_dec(v___x_2220_);
v___x_2222_ = lean_box(v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2206_ = stack[0].m_obj;
lean_object* v___y_2207_ = stack[1].m_obj;
lean_object* v___y_2208_ = stack[2].m_obj;
lean_object* v___y_2209_ = stack[3].m_obj;
lean_object* v___y_2210_ = stack[4].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(v_cls_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed(lean_object* v_cls_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(v_cls_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2232_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(lean_object* v_cls_2235_, lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_ref_2242_; lean_object* v___x_2243_; lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2289_; 
v_ref_2242_ = lean_ctor_get(v___y_2239_, 2);
v___x_2243_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2289_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2289_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v_traceState_2249_; lean_object* v_env_2250_; lean_object* v_nextMacroScope_2251_; lean_object* v_ngen_2252_; lean_object* v_auxDeclNGen_2253_; lean_object* v_cache_2254_; lean_object* v_recordedDeps_2255_; lean_object* v_messages_2256_; lean_object* v_infoState_2257_; lean_object* v_snapshotTasks_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2288_; 
v___x_2248_ = lean_st_ref_take(v___y_2240_);
v_traceState_2249_ = lean_ctor_get(v___x_2248_, 4);
v_env_2250_ = lean_ctor_get(v___x_2248_, 0);
v_nextMacroScope_2251_ = lean_ctor_get(v___x_2248_, 1);
v_ngen_2252_ = lean_ctor_get(v___x_2248_, 2);
v_auxDeclNGen_2253_ = lean_ctor_get(v___x_2248_, 3);
v_cache_2254_ = lean_ctor_get(v___x_2248_, 5);
v_recordedDeps_2255_ = lean_ctor_get(v___x_2248_, 6);
v_messages_2256_ = lean_ctor_get(v___x_2248_, 7);
v_infoState_2257_ = lean_ctor_get(v___x_2248_, 8);
v_snapshotTasks_2258_ = lean_ctor_get(v___x_2248_, 9);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2260_ = v___x_2248_;
v_isShared_2261_ = v_isSharedCheck_2288_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_snapshotTasks_2258_);
lean_inc(v_infoState_2257_);
lean_inc(v_messages_2256_);
lean_inc(v_recordedDeps_2255_);
lean_inc(v_cache_2254_);
lean_inc(v_traceState_2249_);
lean_inc(v_auxDeclNGen_2253_);
lean_inc(v_ngen_2252_);
lean_inc(v_nextMacroScope_2251_);
lean_inc(v_env_2250_);
lean_dec(v___x_2248_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2288_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
uint64_t v_tid_2262_; lean_object* v_traces_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2287_; 
v_tid_2262_ = lean_ctor_get_uint64(v_traceState_2249_, sizeof(void*)*1);
v_traces_2263_ = lean_ctor_get(v_traceState_2249_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_traceState_2249_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2265_ = v_traceState_2249_;
v_isShared_2266_ = v_isSharedCheck_2287_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_traces_2263_);
lean_dec(v_traceState_2249_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2287_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; double v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_float_once(&l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
v___x_2269_ = 0;
v___x_2270_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1));
v___x_2271_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2271_, 0, v_cls_2235_);
lean_ctor_set(v___x_2271_, 1, v___x_2267_);
lean_ctor_set(v___x_2271_, 2, v___x_2270_);
lean_ctor_set_float(v___x_2271_, sizeof(void*)*3, v___x_2268_);
lean_ctor_set_float(v___x_2271_, sizeof(void*)*3 + 8, v___x_2268_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*3 + 16, v___x_2269_);
v___x_2272_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2));
v___x_2273_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v_a_2244_);
lean_ctor_set(v___x_2273_, 2, v___x_2272_);
lean_inc(v_ref_2242_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v_ref_2242_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_PersistentArray_push___redArg(v_traces_2263_, v___x_2274_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2275_);
v___x_2277_ = v___x_2265_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2275_);
lean_ctor_set_uint64(v_reuseFailAlloc_2286_, sizeof(void*)*1, v_tid_2262_);
v___x_2277_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 4, v___x_2277_);
v___x_2279_ = v___x_2260_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_env_2250_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_nextMacroScope_2251_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_ngen_2252_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_auxDeclNGen_2253_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2285_, 5, v_cache_2254_);
lean_ctor_set(v_reuseFailAlloc_2285_, 6, v_recordedDeps_2255_);
lean_ctor_set(v_reuseFailAlloc_2285_, 7, v_messages_2256_);
lean_ctor_set(v_reuseFailAlloc_2285_, 8, v_infoState_2257_);
lean_ctor_set(v_reuseFailAlloc_2285_, 9, v_snapshotTasks_2258_);
v___x_2279_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2280_ = lean_st_ref_put(v___y_2240_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0));
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2281_);
v___x_2283_ = v___x_2246_;
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2235_ = stack[0].m_obj;
lean_object* v_msg_2236_ = stack[1].m_obj;
lean_object* v___y_2237_ = stack[2].m_obj;
lean_object* v___y_2238_ = stack[3].m_obj;
lean_object* v___y_2239_ = stack[4].m_obj;
lean_object* v___y_2240_ = stack[5].m_obj;
lean_object* v_res_2290_;
v_res_2290_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2235_, v_msg_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
stack->m_obj
 = v_res_2290_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___boxed(lean_object* v_cls_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2291_, v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(lean_object* v_cls_2305_, lean_object* v___f_2306_, lean_object* v_00_u03c6_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___y_2314_; lean_object* v___x_2362_; 
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2362_ = lean_apply_5(v___f_2306_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2385_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2385_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2385_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
if (lean_obj_tag(v_a_2363_) == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v___x_2367_ = lean_box(0);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
else
{
lean_object* v_val_2371_; uint8_t v___x_2372_; 
lean_del_object(v___x_2365_);
v_val_2371_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_val_2371_);
lean_dec_ref_known(v_a_2363_, 1);
v___x_2372_ = lean_unbox(v_val_2371_);
lean_dec(v_val_2371_);
if (v___x_2372_ == 0)
{
goto v___jp_2319_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2373_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3);
lean_inc_ref(v_00_u03c6_2307_);
v___x_2374_ = l_Lean_MessageData_ofExpr(v_00_u03c6_2307_);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_inc(v_cls_2305_);
v___x_2376_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2305_, v___x_2375_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_dec_ref_known(v___x_2376_, 1);
goto v___jp_2319_;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v_a_2386_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2362_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2362_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___y_2314_);
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
v___jp_2319_:
{
lean_object* v___x_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_inc_ref(v_00_u03c6_2307_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_00_u03c6_2307_);
v___x_2321_ = 0;
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Lean_Meta_mkFreshExprMVar(v___x_2320_, v___x_2321_, v___x_2322_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_Expr_mvarId_x21(v_a_2324_);
v___x_2326_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2325_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_toCold_2327_; lean_object* v_options_2328_; uint8_t v_hasTrace_2329_; 
lean_dec_ref_known(v___x_2326_, 1);
v_toCold_2327_ = lean_ctor_get(v___y_2310_, 0);
v_options_2328_ = lean_ctor_get(v_toCold_2327_, 2);
v_hasTrace_2329_ = lean_ctor_get_uint8(v_options_2328_, sizeof(void*)*1);
if (v_hasTrace_2329_ == 0)
{
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v___y_2314_ = v_a_2324_;
goto v___jp_2313_;
}
else
{
lean_object* v_inheritedTraceOptions_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_inheritedTraceOptions_2330_ = lean_ctor_get(v_toCold_2327_, 11);
v___x_2331_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__11));
lean_inc(v_cls_2305_);
v___x_2332_ = l_Lean_Name_append(v___x_2331_, v_cls_2305_);
v___x_2333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2330_, v_options_2328_, v___x_2332_);
lean_dec(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v___y_2314_ = v_a_2324_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1);
v___x_2335_ = l_Lean_MessageData_ofExpr(v_00_u03c6_2307_);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2305_, v___x_2336_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_dec_ref_known(v___x_2337_, 1);
v___y_2314_ = v_a_2324_;
goto v___jp_2313_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_a_2324_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2324_);
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v_a_2346_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2326_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2326_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_00_u03c6_2307_);
lean_dec(v_cls_2305_);
v_a_2354_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2323_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2323_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2305_ = stack[0].m_obj;
lean_object* v___f_2306_ = stack[1].m_obj;
lean_object* v_00_u03c6_2307_ = stack[2].m_obj;
lean_object* v___y_2308_ = stack[3].m_obj;
lean_object* v___y_2309_ = stack[4].m_obj;
lean_object* v___y_2310_ = stack[5].m_obj;
lean_object* v___y_2311_ = stack[6].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(v_cls_2305_, v___f_2306_, v_00_u03c6_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed(lean_object* v_cls_2395_, lean_object* v___f_2396_, lean_object* v_00_u03c6_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(v_cls_2395_, v___f_2396_, v_00_u03c6_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(lean_object* v_goal_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___y_2422_; uint8_t v___y_2423_; lean_object* v_cls_2425_; lean_object* v___f_2426_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___x_2453_; lean_object* v_a_2454_; lean_object* v_val_2455_; uint8_t v___x_2456_; 
v_cls_2425_ = ((lean_object*)(l_Lean_MVarId_applyRflAndAndIntro___closed__9));
v___f_2426_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1));
v___x_2453_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(v_cls_2425_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
v_val_2455_ = lean_ctor_get(v_a_2454_, 0);
lean_inc(v_val_2455_);
lean_dec(v_a_2454_);
v___x_2456_ = lean_unbox(v_val_2455_);
lean_dec(v_val_2455_);
if (v___x_2456_ == 0)
{
v___y_2428_ = v_a_2413_;
v___y_2429_ = v_a_2414_;
v___y_2430_ = v_a_2415_;
v___y_2431_ = v_a_2416_;
goto v___jp_2427_;
}
else
{
lean_object* v_target_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_target_2457_ = lean_ctor_get(v_goal_2412_, 3);
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3);
lean_inc_ref(v_target_2457_);
v___x_2459_ = l_Lean_MessageData_ofExpr(v_target_2457_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_2425_, v___x_2460_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_dec_ref_known(v___x_2461_, 1);
v___y_2428_ = v_a_2413_;
v___y_2429_ = v_a_2414_;
v___y_2430_ = v_a_2415_;
v___y_2431_ = v_a_2416_;
goto v___jp_2427_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_goal_2412_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
v___jp_2421_:
{
if (v___y_2423_ == 0)
{
lean_dec_ref(v___y_2422_);
goto v___jp_2418_;
}
else
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___y_2422_);
return v___x_2424_;
}
}
v___jp_2427_:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2412_, v___f_2426_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2449_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2449_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2449_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
if (lean_obj_tag(v_a_2433_) == 0)
{
lean_del_object(v___x_2435_);
goto v___jp_2418_;
}
else
{
lean_object* v_val_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2448_; 
v_val_2437_ = lean_ctor_get(v_a_2433_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_a_2433_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2439_ = v_a_2433_;
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_val_2437_);
lean_dec(v_a_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_snd_2441_; lean_object* v___x_2443_; 
v_snd_2441_ = lean_ctor_get(v_val_2437_, 1);
lean_inc(v_snd_2441_);
lean_dec(v_val_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_snd_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_snd_2441_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2443_);
v___x_2445_ = v___x_2435_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
else
{
lean_object* v_a_2450_; uint8_t v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2451_ = l_Lean_Exception_isInterrupt(v_a_2450_);
if (v___x_2451_ == 0)
{
uint8_t v___x_2452_; 
lean_inc(v_a_2450_);
v___x_2452_ = l_Lean_Exception_isRuntime(v_a_2450_);
v___y_2422_ = v_a_2450_;
v___y_2423_ = v___x_2452_;
goto v___jp_2421_;
}
else
{
v___y_2422_ = v_a_2450_;
v___y_2423_ = v___x_2451_;
goto v___jp_2421_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2412_ = stack[0].m_obj;
lean_object* v_a_2413_ = stack[1].m_obj;
lean_object* v_a_2414_ = stack[2].m_obj;
lean_object* v_a_2415_ = stack[3].m_obj;
lean_object* v_a_2416_ = stack[4].m_obj;
lean_object* v_res_2470_;
v_res_2470_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(v_goal_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
stack->m_obj
 = v_res_2470_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___boxed(lean_object* v_goal_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(v_goal_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2477_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(uint8_t v___y_2478_, lean_object* v_x_2479_){
_start:
{
return v___y_2478_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_2478_ = stack[0].m_num;
lean_object* v_x_2479_ = stack[1].m_obj;
uint8_t v_res_2480_;
v_res_2480_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(v___y_2478_, v_x_2479_);
stack->m_num = v_res_2480_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed(lean_object* v___y_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v___y_9296__boxed_2483_; uint8_t v_res_2484_; lean_object* v_r_2485_; 
v___y_9296__boxed_2483_ = lean_unbox(v___y_2481_);
v_res_2484_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(v___y_9296__boxed_2483_, v_x_2482_);
lean_dec(v_x_2482_);
v_r_2485_ = lean_box(v_res_2484_);
return v_r_2485_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(lean_object* v_00_u03c6_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_00_u03c6_2498_);
v___x_2505_ = 0;
v___x_2506_ = lean_box(0);
v___x_2507_ = l_Lean_Meta_mkFreshExprMVar(v___x_2504_, v___x_2505_, v___x_2506_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2566_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2566_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2566_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = l_Lean_Expr_mvarId_x21(v_a_2508_);
lean_inc(v___x_2519_);
v___x_2520_ = l_Lean_MVarId_applyRflAndAndIntro(v___x_2519_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_dec_ref_known(v___x_2520_, 1);
lean_dec(v___x_2519_);
goto v___jp_2512_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2565_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2565_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2565_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
uint8_t v___y_2526_; uint8_t v___x_2563_; 
v___x_2563_ = l_Lean_Exception_isInterrupt(v_a_2521_);
if (v___x_2563_ == 0)
{
uint8_t v___x_2564_; 
lean_inc(v_a_2521_);
v___x_2564_ = l_Lean_Exception_isRuntime(v_a_2521_);
v___y_2526_ = v___x_2564_;
goto v___jp_2525_;
}
else
{
v___y_2526_ = v___x_2563_;
goto v___jp_2525_;
}
v___jp_2525_:
{
if (v___y_2526_ == 0)
{
lean_object* v_ref_2527_; lean_object* v___x_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_del_object(v___x_2523_);
lean_dec(v_a_2521_);
v_ref_2527_ = lean_ctor_get(v___y_2501_, 2);
v___x_2528_ = lean_box(v___y_2526_);
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2529_, 0, v___x_2528_);
v___x_2530_ = l_Lean_SourceInfo_fromRef(v_ref_2527_, v___y_2526_);
v___x_2531_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1));
v___x_2532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2));
lean_inc(v___x_2530_);
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2530_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_Syntax_node1(v___x_2530_, v___x_2531_, v___x_2533_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_box(0);
v___x_2537_ = 1;
v___x_2538_ = lean_box(1);
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3));
v___x_2540_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_2540_, 0, v___x_2535_);
lean_ctor_set(v___x_2540_, 1, v___x_2536_);
lean_ctor_set(v___x_2540_, 2, v___x_2535_);
lean_ctor_set(v___x_2540_, 3, v___f_2529_);
lean_ctor_set(v___x_2540_, 4, v___x_2538_);
lean_ctor_set(v___x_2540_, 5, v___x_2538_);
lean_ctor_set(v___x_2540_, 6, v___x_2535_);
lean_ctor_set(v___x_2540_, 7, v___x_2539_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8, v___x_2537_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 1, v___x_2537_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 2, v___x_2537_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 3, v___x_2537_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 4, v___y_2526_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 5, v___y_2526_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 6, v___y_2526_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 7, v___y_2526_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 8, v___x_2537_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 9, v___y_2526_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*8 + 10, v___x_2537_);
v___x_2541_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4));
v___x_2542_ = l_Lean_Elab_runTactic(v___x_2519_, v___x_2534_, v___x_2540_, v___x_2541_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_fst_2547_; 
v_fst_2547_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2547_);
lean_dec(v_a_2543_);
if (lean_obj_tag(v_fst_2547_) == 0)
{
lean_del_object(v___x_2545_);
goto v___jp_2512_;
}
else
{
lean_object* v___x_2549_; 
lean_dec(v_fst_2547_);
lean_del_object(v___x_2510_);
lean_dec(v_a_2508_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2535_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2535_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_del_object(v___x_2510_);
lean_dec(v_a_2508_);
v_a_2552_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2542_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2542_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v___x_2561_; 
lean_dec(v___x_2519_);
lean_del_object(v___x_2510_);
lean_dec(v_a_2508_);
if (v_isShared_2524_ == 0)
{
v___x_2561_ = v___x_2523_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2521_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
v___jp_2512_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2513_ = lean_box(0);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v_a_2508_);
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2515_);
v___x_2517_ = v___x_2510_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_a_2567_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2507_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2507_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c6_2498_ = stack[0].m_obj;
lean_object* v___y_2499_ = stack[1].m_obj;
lean_object* v___y_2500_ = stack[2].m_obj;
lean_object* v___y_2501_ = stack[3].m_obj;
lean_object* v___y_2502_ = stack[4].m_obj;
lean_object* v_res_2575_;
v_res_2575_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(v_00_u03c6_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed(lean_object* v_00_u03c6_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(v_00_u03c6_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2582_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(lean_object* v_goal_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___f_2593_; lean_object* v___x_2594_; 
v___f_2593_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0));
v___x_2594_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_2584_, v___f_2593_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2611_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2611_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2611_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
if (lean_obj_tag(v_a_2595_) == 0)
{
lean_del_object(v___x_2597_);
goto v___jp_2590_;
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2610_; 
v_val_2599_ = lean_ctor_get(v_a_2595_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_a_2595_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2601_ = v_a_2595_;
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_val_2599_);
lean_dec(v_a_2595_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_snd_2603_; lean_object* v___x_2605_; 
v_snd_2603_ = lean_ctor_get(v_val_2599_, 1);
lean_inc(v_snd_2603_);
lean_dec(v_val_2599_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_snd_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_snd_2603_);
v___x_2605_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2605_);
v___x_2607_ = v___x_2597_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2623_; 
v_a_2612_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2614_ = v___x_2594_;
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2594_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___y_2617_; uint8_t v___x_2621_; 
v___x_2621_ = l_Lean_Exception_isInterrupt(v_a_2612_);
if (v___x_2621_ == 0)
{
uint8_t v___x_2622_; 
lean_inc(v_a_2612_);
v___x_2622_ = l_Lean_Exception_isRuntime(v_a_2612_);
v___y_2617_ = v___x_2622_;
goto v___jp_2616_;
}
else
{
v___y_2617_ = v___x_2621_;
goto v___jp_2616_;
}
v___jp_2616_:
{
if (v___y_2617_ == 0)
{
lean_del_object(v___x_2614_);
lean_dec(v_a_2612_);
goto v___jp_2590_;
}
else
{
lean_object* v___x_2619_; 
if (v_isShared_2615_ == 0)
{
v___x_2619_ = v___x_2614_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2612_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
v___jp_2590_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2584_ = stack[0].m_obj;
lean_object* v_a_2585_ = stack[1].m_obj;
lean_object* v_a_2586_ = stack[2].m_obj;
lean_object* v_a_2587_ = stack[3].m_obj;
lean_object* v_a_2588_ = stack[4].m_obj;
lean_object* v_res_2624_;
v_res_2624_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(v_goal_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___boxed(lean_object* v_goal_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(v_goal_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2631_;
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
