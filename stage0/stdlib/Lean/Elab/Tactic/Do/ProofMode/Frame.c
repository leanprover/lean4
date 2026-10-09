// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Frame
// Imports: public import Std.Tactic.Do.Syntax public import Lean.Elab.Tactic.Do.ProofMode.Focus
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.Tactic.Do.ProofMode.Frame"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_private.Lean.Elab.Tactic.Do.ProofMode.Frame.0.Lean.Elab.Tactic.Do.ProofMode.transferHypNames.label"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Frame"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "frame"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HasFrame"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Could not infer frame"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 148, 215, 79, 118, 195, 150, 87)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mframe"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 145, 19, 234, 215, 109, 237, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMFrame"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(88, 236, 37, 169, 242, 201, 22, 247)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(lean_object* v_P_1_, lean_object* v_acc_2_){
_start:
{
lean_object* v___x_3_; 
lean_inc_ref(v_P_1_);
v___x_3_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_P_1_);
if (lean_obj_tag(v___x_3_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec_ref(v_P_1_);
v_val_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v___x_3_, 1);
v___x_5_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5_, 0, v_val_4_);
lean_ctor_set(v___x_5_, 1, v_acc_2_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
lean_dec(v___x_3_);
v___x_6_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_P_1_);
lean_dec_ref(v_P_1_);
if (lean_obj_tag(v___x_6_) == 1)
{
lean_object* v_val_7_; lean_object* v_snd_8_; lean_object* v_snd_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_12_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
v_snd_8_ = lean_ctor_get(v_val_7_, 1);
lean_inc(v_snd_8_);
lean_dec(v_val_7_);
v_snd_9_ = lean_ctor_get(v_snd_8_, 1);
lean_inc(v_snd_9_);
lean_dec(v_snd_8_);
v_fst_10_ = lean_ctor_get(v_snd_9_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v_snd_9_, 1);
lean_inc(v_snd_11_);
lean_dec(v_snd_9_);
v___x_12_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_snd_11_, v_acc_2_);
v_P_1_ = v_fst_10_;
v_acc_2_ = v___x_12_;
goto _start;
}
else
{
lean_dec(v___x_6_);
return v_acc_2_;
}
}
}
}
lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(lean_object* v___y_14_){
_start:
{
lean_object* v___x_16_; lean_object* v_ngen_17_; lean_object* v_namePrefix_18_; lean_object* v_idx_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_49_; 
v___x_16_ = lean_st_ref_get(v___y_14_);
v_ngen_17_ = lean_ctor_get(v___x_16_, 2);
lean_inc_ref(v_ngen_17_);
lean_dec(v___x_16_);
v_namePrefix_18_ = lean_ctor_get(v_ngen_17_, 0);
v_idx_19_ = lean_ctor_get(v_ngen_17_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_ngen_17_);
if (v_isSharedCheck_49_ == 0)
{
v___x_21_ = v_ngen_17_;
v_isShared_22_ = v_isSharedCheck_49_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_idx_19_);
lean_inc(v_namePrefix_18_);
lean_dec(v_ngen_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_49_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v_r_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
lean_inc(v_idx_19_);
lean_inc(v_namePrefix_18_);
v_r_23_ = l_Lean_Name_num___override(v_namePrefix_18_, v_idx_19_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_add(v_idx_19_, v___x_24_);
lean_dec(v_idx_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_25_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_namePrefix_18_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_25_);
v___x_27_ = v_reuseFailAlloc_48_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; lean_object* v_env_29_; lean_object* v_nextMacroScope_30_; lean_object* v_auxDeclNGen_31_; lean_object* v_traceState_32_; lean_object* v_cache_33_; lean_object* v_recordedDeps_34_; lean_object* v_messages_35_; lean_object* v_infoState_36_; lean_object* v_snapshotTasks_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_46_; 
v___x_28_ = lean_st_ref_take(v___y_14_);
v_env_29_ = lean_ctor_get(v___x_28_, 0);
v_nextMacroScope_30_ = lean_ctor_get(v___x_28_, 1);
v_auxDeclNGen_31_ = lean_ctor_get(v___x_28_, 3);
v_traceState_32_ = lean_ctor_get(v___x_28_, 4);
v_cache_33_ = lean_ctor_get(v___x_28_, 5);
v_recordedDeps_34_ = lean_ctor_get(v___x_28_, 6);
v_messages_35_ = lean_ctor_get(v___x_28_, 7);
v_infoState_36_ = lean_ctor_get(v___x_28_, 8);
v_snapshotTasks_37_ = lean_ctor_get(v___x_28_, 9);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; 
v_unused_47_ = lean_ctor_get(v___x_28_, 2);
lean_dec(v_unused_47_);
v___x_39_ = v___x_28_;
v_isShared_40_ = v_isSharedCheck_46_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_snapshotTasks_37_);
lean_inc(v_infoState_36_);
lean_inc(v_messages_35_);
lean_inc(v_recordedDeps_34_);
lean_inc(v_cache_33_);
lean_inc(v_traceState_32_);
lean_inc(v_auxDeclNGen_31_);
lean_inc(v_nextMacroScope_30_);
lean_inc(v_env_29_);
lean_dec(v___x_28_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_46_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 2, v___x_27_);
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_29_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_30_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_31_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v_traceState_32_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v_cache_33_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_recordedDeps_34_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_messages_35_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_infoState_36_);
lean_ctor_set(v_reuseFailAlloc_45_, 9, v_snapshotTasks_37_);
v___x_42_ = v_reuseFailAlloc_45_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_st_ref_put(v___y_14_, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_r_23_);
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_14_ = stack[0].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_14_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg___boxed(lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_51_);
lean_dec(v___y_51_);
return v_res_53_;
}
}
lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_57_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_54_ = stack[0].m_obj;
lean_object* v___y_55_ = stack[1].m_obj;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v___y_57_ = stack[3].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(v___y_54_, v___y_55_, v___y_56_, v___y_57_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___boxed(lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_66_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(lean_object* v_msg_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_3046__overap_75_; lean_object* v___x_76_; 
v___f_74_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0));
v___x_3046__overap_75_ = lean_panic_fn_borrowed(v___f_74_, v_msg_68_);
lean_inc(v___y_72_);
lean_inc_ref(v___y_71_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
v___x_76_ = lean_apply_5(v___x_3046__overap_75_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_68_ = stack[0].m_obj;
lean_object* v___y_69_ = stack[1].m_obj;
lean_object* v___y_70_ = stack[2].m_obj;
lean_object* v___y_71_ = stack[3].m_obj;
lean_object* v___y_72_ = stack[4].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v_msg_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___boxed(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v_msg_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_84_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(lean_object* v_a_88_, lean_object* v_Ps_89_, lean_object* v_a_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_182_; 
v_snd_96_ = lean_ctor_get(v_a_90_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_a_90_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_a_90_, 0);
lean_dec(v_unused_183_);
v___x_98_ = v_a_90_;
v_isShared_99_ = v_isSharedCheck_182_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_dec(v_a_90_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_182_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_box(0);
v___x_101_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_102_ = l_Lean_Core_mkFreshUserName(v___x_101_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_94_);
if (lean_obj_tag(v___x_104_) == 0)
{
if (lean_obj_tag(v_snd_96_) == 1)
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref_known(v___x_104_, 1);
lean_dec(v_a_103_);
v_head_105_ = lean_ctor_get(v_snd_96_, 0);
v_tail_106_ = lean_ctor_get(v_snd_96_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_snd_96_);
if (v_isSharedCheck_150_ == 0)
{
v___x_108_ = v_snd_96_;
v_isShared_109_ = v_isSharedCheck_150_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_tail_106_);
lean_inc(v_head_105_);
lean_dec(v_snd_96_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_150_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_name_110_; lean_object* v_uniq_111_; lean_object* v_p_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_149_; 
v_name_110_ = lean_ctor_get(v_head_105_, 0);
v_uniq_111_ = lean_ctor_get(v_head_105_, 1);
v_p_112_ = lean_ctor_get(v_head_105_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v_head_105_);
if (v_isSharedCheck_149_ == 0)
{
v___x_114_ = v_head_105_;
v_isShared_115_ = v_isSharedCheck_149_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_p_112_);
lean_inc(v_uniq_111_);
lean_inc(v_name_110_);
lean_dec(v_head_105_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_149_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; 
lean_inc_ref(v_a_88_);
v___x_116_ = l_Lean_Meta_isExprDefEq(v_p_112_, v_a_88_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_140_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_140_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_140_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_140_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v___x_121_; 
v___x_121_ = lean_unbox(v_a_117_);
lean_dec(v_a_117_);
if (v___x_121_ == 0)
{
lean_object* v___x_123_; 
lean_del_object(v___x_119_);
lean_del_object(v___x_114_);
lean_dec(v_uniq_111_);
lean_dec(v_name_110_);
lean_del_object(v___x_108_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_tail_106_);
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_123_ = v___x_98_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_tail_106_);
v___x_123_ = v_reuseFailAlloc_125_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
v_a_90_ = v___x_123_;
goto _start;
}
}
else
{
lean_object* v___x_127_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 2, v_a_88_);
v___x_127_ = v___x_114_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_name_110_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_uniq_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_a_88_);
v___x_127_ = v_reuseFailAlloc_139_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_127_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_128_);
lean_ctor_set(v___x_98_, 0, v_Ps_89_);
v___x_130_ = v___x_98_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_Ps_89_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_138_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 0);
lean_ctor_set(v___x_108_, 0, v___x_131_);
v___x_133_ = v___x_108_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_tail_106_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_133_);
v___x_135_ = v___x_119_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_del_object(v___x_114_);
lean_dec(v_uniq_111_);
lean_dec(v_name_110_);
lean_del_object(v___x_108_);
lean_dec(v_tail_106_);
lean_del_object(v___x_98_);
lean_dec(v_Ps_89_);
lean_dec_ref(v_a_88_);
v_a_141_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_116_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_116_);
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
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_165_; 
v_a_151_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_165_ == 0)
{
v___x_153_ = v___x_104_;
v_isShared_154_ = v_isSharedCheck_165_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_104_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_165_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v_a_103_);
lean_ctor_set(v___x_155_, 1, v_a_151_);
lean_ctor_set(v___x_155_, 2, v_a_88_);
v___x_156_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_155_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_156_);
lean_ctor_set(v___x_98_, 0, v_Ps_89_);
v___x_158_ = v___x_98_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_Ps_89_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_164_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_snd_96_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_160_);
v___x_162_ = v___x_153_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_a_103_);
lean_del_object(v___x_98_);
lean_dec(v_snd_96_);
lean_dec(v_Ps_89_);
lean_dec_ref(v_a_88_);
v_a_166_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_104_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_104_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_del_object(v___x_98_);
lean_dec(v_snd_96_);
lean_dec(v_Ps_89_);
lean_dec_ref(v_a_88_);
v_a_174_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_102_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_102_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_88_ = stack[0].m_obj;
lean_object* v_Ps_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v___y_91_ = stack[3].m_obj;
lean_object* v___y_92_ = stack[4].m_obj;
lean_object* v___y_93_ = stack[5].m_obj;
lean_object* v___y_94_ = stack[6].m_obj;
lean_object* v_res_184_;
v_res_184_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_88_, v_Ps_89_, v_a_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___boxed(lean_object* v_a_185_, lean_object* v_Ps_186_, lean_object* v_a_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_185_, v_Ps_186_, v_a_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2));
v___x_198_ = lean_unsigned_to_nat(8u);
v___x_199_ = lean_unsigned_to_nat(51u);
v___x_200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1));
v___x_201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0));
v___x_202_ = l_mkPanicMessageWithDecl(v___x_201_, v___x_200_, v___x_199_, v___x_198_, v___x_197_);
return v___x_202_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(lean_object* v_Ps_203_, lean_object* v_P_x27_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_P_x27_204_, v_a_206_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_274_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_274_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_274_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_274_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; 
lean_inc(v_a_211_);
v___x_215_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_211_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v___x_216_; lean_object* v___x_218_; 
lean_dec_ref_known(v___x_215_, 1);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_Ps_203_);
lean_ctor_set(v___x_216_, 1, v_a_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_216_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
else
{
lean_object* v___x_220_; 
lean_dec(v___x_215_);
lean_del_object(v___x_213_);
v___x_220_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_211_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v_val_221_; lean_object* v_snd_222_; lean_object* v_snd_223_; lean_object* v_fst_224_; lean_object* v_fst_225_; lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; 
lean_dec(v_a_211_);
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
v_snd_222_ = lean_ctor_get(v_val_221_, 1);
lean_inc(v_snd_222_);
v_snd_223_ = lean_ctor_get(v_snd_222_, 1);
lean_inc(v_snd_223_);
v_fst_224_ = lean_ctor_get(v_val_221_, 0);
lean_inc(v_fst_224_);
lean_dec(v_val_221_);
v_fst_225_ = lean_ctor_get(v_snd_222_, 0);
lean_inc(v_fst_225_);
lean_dec(v_snd_222_);
v_fst_226_ = lean_ctor_get(v_snd_223_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_snd_223_, 1);
lean_inc(v_snd_227_);
lean_dec(v_snd_223_);
v___x_228_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_203_, v_fst_226_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_232_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v_fst_230_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_a_229_, 1);
lean_inc(v_snd_231_);
lean_dec(v_a_229_);
v___x_232_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_fst_230_, v_snd_227_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_250_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_250_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_250_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_250_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
v_fst_237_ = lean_ctor_get(v_a_233_, 0);
v_snd_238_ = lean_ctor_get(v_a_233_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_249_ == 0)
{
v___x_240_ = v_a_233_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snd_238_);
lean_inc(v_fst_237_);
lean_dec(v_a_233_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_224_, v_fst_225_, v_snd_231_, v_snd_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_244_);
v___x_246_ = v___x_235_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
else
{
lean_dec(v_snd_231_);
lean_dec(v_fst_225_);
lean_dec(v_fst_224_);
return v___x_232_;
}
}
else
{
lean_dec(v_snd_227_);
lean_dec(v_fst_225_);
lean_dec(v_fst_224_);
return v___x_228_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v___x_220_);
v___x_251_ = lean_box(0);
lean_inc(v_Ps_203_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_Ps_203_);
v___x_253_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_211_, v_Ps_203_, v___x_252_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_265_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_265_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_fst_258_; 
v_fst_258_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_fst_258_);
lean_dec(v_a_254_);
if (lean_obj_tag(v_fst_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_del_object(v___x_256_);
v___x_259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3);
v___x_260_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v___x_259_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v___x_263_; 
v_val_261_ = lean_ctor_get(v_fst_258_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_fst_258_, 1);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v_val_261_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_val_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_253_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_253_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_Ps_203_);
v_a_275_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_210_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_210_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_0interp(lean_interpreter_value* stack)
{
lean_object* v_Ps_203_ = stack[0].m_obj;
lean_object* v_P_x27_204_ = stack[1].m_obj;
lean_object* v_a_205_ = stack[2].m_obj;
lean_object* v_a_206_ = stack[3].m_obj;
lean_object* v_a_207_ = stack[4].m_obj;
lean_object* v_a_208_ = stack[5].m_obj;
lean_object* v_res_283_;
v_res_283_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_203_, v_P_x27_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___boxed(lean_object* v_Ps_284_, lean_object* v_P_x27_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_284_, v_P_x27_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_291_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(lean_object* v_a_292_, lean_object* v_Ps_293_, lean_object* v_inst_294_, lean_object* v_a_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_292_, v_Ps_293_, v_a_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_292_ = stack[0].m_obj;
lean_object* v_Ps_293_ = stack[1].m_obj;
lean_object* v_a_295_ = stack[3].m_obj;
lean_object* v___y_296_ = stack[4].m_obj;
lean_object* v___y_297_ = stack[5].m_obj;
lean_object* v___y_298_ = stack[6].m_obj;
lean_object* v___y_299_ = stack[7].m_obj;
lean_object* v_res_302_;
v_res_302_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(v_a_292_, v_Ps_293_, lean_box(0), v_a_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___boxed(lean_object* v_a_303_, lean_object* v_Ps_304_, lean_object* v_inst_305_, lean_object* v_a_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(v_a_303_, v_Ps_304_, v_inst_305_, v_a_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_312_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(lean_object* v_P_313_, lean_object* v_P_x27_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
v___x_321_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_P_313_, v___x_320_);
v___x_322_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v___x_321_, v_P_x27_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_snd_327_; lean_object* v___x_329_; 
v_snd_327_ = lean_ctor_get(v_a_323_, 1);
lean_inc(v_snd_327_);
lean_dec(v_a_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v_snd_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_snd_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_322_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_322_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_313_ = stack[0].m_obj;
lean_object* v_P_x27_314_ = stack[1].m_obj;
lean_object* v_a_315_ = stack[2].m_obj;
lean_object* v_a_316_ = stack[3].m_obj;
lean_object* v_a_317_ = stack[4].m_obj;
lean_object* v_a_318_ = stack[5].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_P_313_, v_P_x27_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed(lean_object* v_P_341_, lean_object* v_P_x27_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_P_341_, v_P_x27_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0(lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v___x_353_, lean_object* v___x_354_, lean_object* v___x_355_, lean_object* v_00_u03c3s_356_, lean_object* v_hyps_357_, lean_object* v_P_x27_358_, lean_object* v_target_359_, lean_object* v_00_u03c6_360_, lean_object* v_a_361_, lean_object* v_toPure_362_, lean_object* v_prf_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_prf_368_; lean_object* v___x_369_; 
v___x_364_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_366_ = l_Lean_Name_mkStr6(v___x_351_, v___x_352_, v___x_353_, v___x_354_, v___x_364_, v___x_365_);
v___x_367_ = l_Lean_mkConst(v___x_366_, v___x_355_);
v_prf_368_ = l_Lean_mkApp7(v___x_367_, v_00_u03c3s_356_, v_hyps_357_, v_P_x27_358_, v_target_359_, v_00_u03c6_360_, v_a_361_, v_prf_363_);
v___x_369_ = lean_apply_2(v_toPure_362_, lean_box(0), v_prf_368_);
return v___x_369_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(lean_object* v_h_u03c6_370_, uint8_t v_____do__lift_371_, uint8_t v___x_372_, lean_object* v_inst_373_, lean_object* v_toBind_374_, lean_object* v___f_375_, lean_object* v_prf_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_mk_empty_array_with_capacity(v___x_377_);
v___x_379_ = lean_array_push(v___x_378_, v_h_u03c6_370_);
v___x_380_ = 1;
v___x_381_ = lean_box(v_____do__lift_371_);
v___x_382_ = lean_box(v___x_372_);
v___x_383_ = lean_box(v_____do__lift_371_);
v___x_384_ = lean_box(v___x_372_);
v___x_385_ = lean_box(v___x_380_);
v___x_386_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_386_, 0, v___x_379_);
lean_closure_set(v___x_386_, 1, v_prf_376_);
lean_closure_set(v___x_386_, 2, v___x_381_);
lean_closure_set(v___x_386_, 3, v___x_382_);
lean_closure_set(v___x_386_, 4, v___x_383_);
lean_closure_set(v___x_386_, 5, v___x_384_);
lean_closure_set(v___x_386_, 6, v___x_385_);
v___x_387_ = lean_apply_2(v_inst_373_, lean_box(0), v___x_386_);
v___x_388_ = lean_apply_4(v_toBind_374_, lean_box(0), lean_box(0), v___x_387_, v___f_375_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u03c6_370_ = stack[0].m_obj;
uint8_t v_____do__lift_371_ = stack[1].m_num;
uint8_t v___x_372_ = stack[2].m_num;
lean_object* v_inst_373_ = stack[3].m_obj;
lean_object* v_toBind_374_ = stack[4].m_obj;
lean_object* v___f_375_ = stack[5].m_obj;
lean_object* v_prf_376_ = stack[6].m_obj;
lean_object* v_res_389_;
v_res_389_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(v_h_u03c6_370_, v_____do__lift_371_, v___x_372_, v_inst_373_, v_toBind_374_, v___f_375_, v_prf_376_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed(lean_object* v_h_u03c6_390_, lean_object* v_____do__lift_391_, lean_object* v___x_392_, lean_object* v_inst_393_, lean_object* v_toBind_394_, lean_object* v___f_395_, lean_object* v_prf_396_){
_start:
{
uint8_t v_____do__lift_405__boxed_397_; uint8_t v___x_406__boxed_398_; lean_object* v_res_399_; 
v_____do__lift_405__boxed_397_ = lean_unbox(v_____do__lift_391_);
v___x_406__boxed_398_ = lean_unbox(v___x_392_);
v_res_399_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(v_h_u03c6_390_, v_____do__lift_405__boxed_397_, v___x_406__boxed_398_, v_inst_393_, v_toBind_394_, v___f_395_, v_prf_396_);
return v_res_399_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(uint8_t v_____do__lift_400_, uint8_t v___x_401_, lean_object* v_inst_402_, lean_object* v_toBind_403_, lean_object* v___f_404_, lean_object* v_kSuccess_405_, lean_object* v_00_u03c6_406_, lean_object* v_goal_407_, lean_object* v_h_u03c6_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_409_ = lean_box(v_____do__lift_400_);
v___x_410_ = lean_box(v___x_401_);
lean_inc(v_toBind_403_);
lean_inc_ref(v_h_u03c6_408_);
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_411_, 0, v_h_u03c6_408_);
lean_closure_set(v___f_411_, 1, v___x_409_);
lean_closure_set(v___f_411_, 2, v___x_410_);
lean_closure_set(v___f_411_, 3, v_inst_402_);
lean_closure_set(v___f_411_, 4, v_toBind_403_);
lean_closure_set(v___f_411_, 5, v___f_404_);
v___x_412_ = lean_apply_3(v_kSuccess_405_, v_00_u03c6_406_, v_h_u03c6_408_, v_goal_407_);
v___x_413_ = lean_apply_4(v_toBind_403_, lean_box(0), lean_box(0), v___x_412_, v___f_411_);
return v___x_413_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_400_ = stack[0].m_num;
uint8_t v___x_401_ = stack[1].m_num;
lean_object* v_inst_402_ = stack[2].m_obj;
lean_object* v_toBind_403_ = stack[3].m_obj;
lean_object* v___f_404_ = stack[4].m_obj;
lean_object* v_kSuccess_405_ = stack[5].m_obj;
lean_object* v_00_u03c6_406_ = stack[6].m_obj;
lean_object* v_goal_407_ = stack[7].m_obj;
lean_object* v_h_u03c6_408_ = stack[8].m_obj;
lean_object* v_res_414_;
v_res_414_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(v_____do__lift_400_, v___x_401_, v_inst_402_, v_toBind_403_, v___f_404_, v_kSuccess_405_, v_00_u03c6_406_, v_goal_407_, v_h_u03c6_408_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed(lean_object* v_____do__lift_415_, lean_object* v___x_416_, lean_object* v_inst_417_, lean_object* v_toBind_418_, lean_object* v___f_419_, lean_object* v_kSuccess_420_, lean_object* v_00_u03c6_421_, lean_object* v_goal_422_, lean_object* v_h_u03c6_423_){
_start:
{
uint8_t v_____do__lift_461__boxed_424_; uint8_t v___x_462__boxed_425_; lean_object* v_res_426_; 
v_____do__lift_461__boxed_424_ = lean_unbox(v_____do__lift_415_);
v___x_462__boxed_425_ = lean_unbox(v___x_416_);
v_res_426_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(v_____do__lift_461__boxed_424_, v___x_462__boxed_425_, v_inst_417_, v_toBind_418_, v___f_419_, v_kSuccess_420_, v_00_u03c6_421_, v_goal_422_, v_h_u03c6_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_00_u03c6_429_, lean_object* v___f_430_, lean_object* v_____do__lift_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_427_, v_inst_428_, v_____do__lift_431_, v_00_u03c6_429_, v___f_430_);
return v___x_432_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(lean_object* v___x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Core_mkFreshUserName(v___x_433_, v___y_436_, v___y_437_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_433_ = stack[0].m_obj;
lean_object* v___y_434_ = stack[1].m_obj;
lean_object* v___y_435_ = stack[2].m_obj;
lean_object* v___y_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v_res_440_;
v_res_440_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(v___x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed(lean_object* v___x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(v___x_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v___x_454_, lean_object* v_00_u03c3s_455_, lean_object* v_hyps_456_, lean_object* v_target_457_, lean_object* v_00_u03c6_458_, lean_object* v_a_459_, lean_object* v_toPure_460_, lean_object* v_u_461_, uint8_t v_____do__lift_462_, uint8_t v___x_463_, lean_object* v_inst_464_, lean_object* v_toBind_465_, lean_object* v_kSuccess_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_P_x27_469_){
_start:
{
lean_object* v___f_470_; lean_object* v_goal_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v___f_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_inc_ref_n(v_00_u03c6_458_, 2);
lean_inc_ref(v_target_457_);
lean_inc_ref(v_P_x27_469_);
lean_inc_ref(v_00_u03c3s_455_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0), 13, 12);
lean_closure_set(v___f_470_, 0, v___x_450_);
lean_closure_set(v___f_470_, 1, v___x_451_);
lean_closure_set(v___f_470_, 2, v___x_452_);
lean_closure_set(v___f_470_, 3, v___x_453_);
lean_closure_set(v___f_470_, 4, v___x_454_);
lean_closure_set(v___f_470_, 5, v_00_u03c3s_455_);
lean_closure_set(v___f_470_, 6, v_hyps_456_);
lean_closure_set(v___f_470_, 7, v_P_x27_469_);
lean_closure_set(v___f_470_, 8, v_target_457_);
lean_closure_set(v___f_470_, 9, v_00_u03c6_458_);
lean_closure_set(v___f_470_, 10, v_a_459_);
lean_closure_set(v___f_470_, 11, v_toPure_460_);
v_goal_471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_471_, 0, v_u_461_);
lean_ctor_set(v_goal_471_, 1, v_00_u03c3s_455_);
lean_ctor_set(v_goal_471_, 2, v_P_x27_469_);
lean_ctor_set(v_goal_471_, 3, v_target_457_);
v___x_472_ = lean_box(v_____do__lift_462_);
v___x_473_ = lean_box(v___x_463_);
lean_inc(v_toBind_465_);
lean_inc(v_inst_464_);
v___f_474_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_474_, 0, v___x_472_);
lean_closure_set(v___f_474_, 1, v___x_473_);
lean_closure_set(v___f_474_, 2, v_inst_464_);
lean_closure_set(v___f_474_, 3, v_toBind_465_);
lean_closure_set(v___f_474_, 4, v___f_470_);
lean_closure_set(v___f_474_, 5, v_kSuccess_466_);
lean_closure_set(v___f_474_, 6, v_00_u03c6_458_);
lean_closure_set(v___f_474_, 7, v_goal_471_);
v___f_475_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_475_, 0, v_inst_467_);
lean_closure_set(v___f_475_, 1, v_inst_468_);
lean_closure_set(v___f_475_, 2, v_00_u03c6_458_);
lean_closure_set(v___f_475_, 3, v___f_474_);
v___f_476_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0));
v___x_477_ = lean_apply_2(v_inst_464_, lean_box(0), v___f_476_);
v___x_478_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_477_, v___f_475_);
return v___x_478_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_450_ = stack[0].m_obj;
lean_object* v___x_451_ = stack[1].m_obj;
lean_object* v___x_452_ = stack[2].m_obj;
lean_object* v___x_453_ = stack[3].m_obj;
lean_object* v___x_454_ = stack[4].m_obj;
lean_object* v_00_u03c3s_455_ = stack[5].m_obj;
lean_object* v_hyps_456_ = stack[6].m_obj;
lean_object* v_target_457_ = stack[7].m_obj;
lean_object* v_00_u03c6_458_ = stack[8].m_obj;
lean_object* v_a_459_ = stack[9].m_obj;
lean_object* v_toPure_460_ = stack[10].m_obj;
lean_object* v_u_461_ = stack[11].m_obj;
uint8_t v_____do__lift_462_ = stack[12].m_num;
uint8_t v___x_463_ = stack[13].m_num;
lean_object* v_inst_464_ = stack[14].m_obj;
lean_object* v_toBind_465_ = stack[15].m_obj;
lean_object* v_kSuccess_466_ = stack[16].m_obj;
lean_object* v_inst_467_ = stack[17].m_obj;
lean_object* v_inst_468_ = stack[18].m_obj;
lean_object* v_P_x27_469_ = stack[19].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(v___x_450_, v___x_451_, v___x_452_, v___x_453_, v___x_454_, v_00_u03c3s_455_, v_hyps_456_, v_target_457_, v_00_u03c6_458_, v_a_459_, v_toPure_460_, v_u_461_, v_____do__lift_462_, v___x_463_, v_inst_464_, v_toBind_465_, v_kSuccess_466_, v_inst_467_, v_inst_468_, v_P_x27_469_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_480_ = _args[0];
lean_object* v___x_481_ = _args[1];
lean_object* v___x_482_ = _args[2];
lean_object* v___x_483_ = _args[3];
lean_object* v___x_484_ = _args[4];
lean_object* v_00_u03c3s_485_ = _args[5];
lean_object* v_hyps_486_ = _args[6];
lean_object* v_target_487_ = _args[7];
lean_object* v_00_u03c6_488_ = _args[8];
lean_object* v_a_489_ = _args[9];
lean_object* v_toPure_490_ = _args[10];
lean_object* v_u_491_ = _args[11];
lean_object* v_____do__lift_492_ = _args[12];
lean_object* v___x_493_ = _args[13];
lean_object* v_inst_494_ = _args[14];
lean_object* v_toBind_495_ = _args[15];
lean_object* v_kSuccess_496_ = _args[16];
lean_object* v_inst_497_ = _args[17];
lean_object* v_inst_498_ = _args[18];
lean_object* v_P_x27_499_ = _args[19];
_start:
{
uint8_t v_____do__lift_557__boxed_500_; uint8_t v___x_558__boxed_501_; lean_object* v_res_502_; 
v_____do__lift_557__boxed_500_ = lean_unbox(v_____do__lift_492_);
v___x_558__boxed_501_ = lean_unbox(v___x_493_);
v_res_502_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(v___x_480_, v___x_481_, v___x_482_, v___x_483_, v___x_484_, v_00_u03c3s_485_, v_hyps_486_, v_target_487_, v_00_u03c6_488_, v_a_489_, v_toPure_490_, v_u_491_, v_____do__lift_557__boxed_500_, v___x_558__boxed_501_, v_inst_494_, v_toBind_495_, v_kSuccess_496_, v_inst_497_, v_inst_498_, v_P_x27_499_);
return v_res_502_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_00_u03c3s_508_, lean_object* v_hyps_509_, lean_object* v_target_510_, lean_object* v_00_u03c6_511_, lean_object* v_a_512_, lean_object* v_toPure_513_, lean_object* v_u_514_, lean_object* v_inst_515_, lean_object* v_toBind_516_, lean_object* v_kSuccess_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_P_x27_520_, lean_object* v_kFail_521_, uint8_t v_____do__lift_522_){
_start:
{
if (v_____do__lift_522_ == 0)
{
uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = 1;
v___x_524_ = lean_box(v_____do__lift_522_);
v___x_525_ = lean_box(v___x_523_);
lean_inc(v_toBind_516_);
lean_inc(v_inst_515_);
lean_inc_ref(v_hyps_509_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed), 20, 19);
lean_closure_set(v___f_526_, 0, v___x_503_);
lean_closure_set(v___f_526_, 1, v___x_504_);
lean_closure_set(v___f_526_, 2, v___x_505_);
lean_closure_set(v___f_526_, 3, v___x_506_);
lean_closure_set(v___f_526_, 4, v___x_507_);
lean_closure_set(v___f_526_, 5, v_00_u03c3s_508_);
lean_closure_set(v___f_526_, 6, v_hyps_509_);
lean_closure_set(v___f_526_, 7, v_target_510_);
lean_closure_set(v___f_526_, 8, v_00_u03c6_511_);
lean_closure_set(v___f_526_, 9, v_a_512_);
lean_closure_set(v___f_526_, 10, v_toPure_513_);
lean_closure_set(v___f_526_, 11, v_u_514_);
lean_closure_set(v___f_526_, 12, v___x_524_);
lean_closure_set(v___f_526_, 13, v___x_525_);
lean_closure_set(v___f_526_, 14, v_inst_515_);
lean_closure_set(v___f_526_, 15, v_toBind_516_);
lean_closure_set(v___f_526_, 16, v_kSuccess_517_);
lean_closure_set(v___f_526_, 17, v_inst_518_);
lean_closure_set(v___f_526_, 18, v_inst_519_);
v___x_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed), 7, 2);
lean_closure_set(v___x_527_, 0, v_hyps_509_);
lean_closure_set(v___x_527_, 1, v_P_x27_520_);
v___x_528_ = lean_apply_2(v_inst_515_, lean_box(0), v___x_527_);
v___x_529_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_528_, v___f_526_);
return v___x_529_;
}
else
{
lean_dec_ref(v_P_x27_520_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
lean_dec(v_kSuccess_517_);
lean_dec(v_toBind_516_);
lean_dec(v_inst_515_);
lean_dec(v_u_514_);
lean_dec(v_toPure_513_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_00_u03c6_511_);
lean_dec_ref(v_target_510_);
lean_dec_ref(v_hyps_509_);
lean_dec_ref(v_00_u03c3s_508_);
lean_dec(v___x_507_);
lean_dec_ref(v___x_506_);
lean_dec_ref(v___x_505_);
lean_dec_ref(v___x_504_);
lean_dec_ref(v___x_503_);
lean_inc(v_kFail_521_);
return v_kFail_521_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_503_ = stack[0].m_obj;
lean_object* v___x_504_ = stack[1].m_obj;
lean_object* v___x_505_ = stack[2].m_obj;
lean_object* v___x_506_ = stack[3].m_obj;
lean_object* v___x_507_ = stack[4].m_obj;
lean_object* v_00_u03c3s_508_ = stack[5].m_obj;
lean_object* v_hyps_509_ = stack[6].m_obj;
lean_object* v_target_510_ = stack[7].m_obj;
lean_object* v_00_u03c6_511_ = stack[8].m_obj;
lean_object* v_a_512_ = stack[9].m_obj;
lean_object* v_toPure_513_ = stack[10].m_obj;
lean_object* v_u_514_ = stack[11].m_obj;
lean_object* v_inst_515_ = stack[12].m_obj;
lean_object* v_toBind_516_ = stack[13].m_obj;
lean_object* v_kSuccess_517_ = stack[14].m_obj;
lean_object* v_inst_518_ = stack[15].m_obj;
lean_object* v_inst_519_ = stack[16].m_obj;
lean_object* v_P_x27_520_ = stack[17].m_obj;
lean_object* v_kFail_521_ = stack[18].m_obj;
uint8_t v_____do__lift_522_ = stack[19].m_num;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(v___x_503_, v___x_504_, v___x_505_, v___x_506_, v___x_507_, v_00_u03c3s_508_, v_hyps_509_, v_target_510_, v_00_u03c6_511_, v_a_512_, v_toPure_513_, v_u_514_, v_inst_515_, v_toBind_516_, v_kSuccess_517_, v_inst_518_, v_inst_519_, v_P_x27_520_, v_kFail_521_, v_____do__lift_522_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_531_ = _args[0];
lean_object* v___x_532_ = _args[1];
lean_object* v___x_533_ = _args[2];
lean_object* v___x_534_ = _args[3];
lean_object* v___x_535_ = _args[4];
lean_object* v_00_u03c3s_536_ = _args[5];
lean_object* v_hyps_537_ = _args[6];
lean_object* v_target_538_ = _args[7];
lean_object* v_00_u03c6_539_ = _args[8];
lean_object* v_a_540_ = _args[9];
lean_object* v_toPure_541_ = _args[10];
lean_object* v_u_542_ = _args[11];
lean_object* v_inst_543_ = _args[12];
lean_object* v_toBind_544_ = _args[13];
lean_object* v_kSuccess_545_ = _args[14];
lean_object* v_inst_546_ = _args[15];
lean_object* v_inst_547_ = _args[16];
lean_object* v_P_x27_548_ = _args[17];
lean_object* v_kFail_549_ = _args[18];
lean_object* v_____do__lift_550_ = _args[19];
_start:
{
uint8_t v_____do__lift_643__boxed_551_; lean_object* v_res_552_; 
v_____do__lift_643__boxed_551_ = lean_unbox(v_____do__lift_550_);
v_res_552_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(v___x_531_, v___x_532_, v___x_533_, v___x_534_, v___x_535_, v_00_u03c3s_536_, v_hyps_537_, v_target_538_, v_00_u03c6_539_, v_a_540_, v_toPure_541_, v_u_542_, v_inst_543_, v_toBind_544_, v_kSuccess_545_, v_inst_546_, v_inst_547_, v_P_x27_548_, v_kFail_549_, v_____do__lift_643__boxed_551_);
lean_dec(v_kFail_549_);
return v_res_552_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v_00_u03c3s_561_, lean_object* v_hyps_562_, lean_object* v_target_563_, lean_object* v_00_u03c6_564_, lean_object* v_toPure_565_, lean_object* v_u_566_, lean_object* v_inst_567_, lean_object* v_toBind_568_, lean_object* v_kSuccess_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_P_x27_572_, lean_object* v_kFail_573_, lean_object* v___x_574_, lean_object* v_____do__lift_575_){
_start:
{
if (lean_obj_tag(v_____do__lift_575_) == 1)
{
lean_object* v_a_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_576_ = lean_ctor_get(v_____do__lift_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v_____do__lift_575_, 1);
lean_inc(v_toBind_568_);
lean_inc(v_inst_567_);
lean_inc_ref(v_00_u03c6_564_);
v___f_577_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed), 20, 19);
lean_closure_set(v___f_577_, 0, v___x_556_);
lean_closure_set(v___f_577_, 1, v___x_557_);
lean_closure_set(v___f_577_, 2, v___x_558_);
lean_closure_set(v___f_577_, 3, v___x_559_);
lean_closure_set(v___f_577_, 4, v___x_560_);
lean_closure_set(v___f_577_, 5, v_00_u03c3s_561_);
lean_closure_set(v___f_577_, 6, v_hyps_562_);
lean_closure_set(v___f_577_, 7, v_target_563_);
lean_closure_set(v___f_577_, 8, v_00_u03c6_564_);
lean_closure_set(v___f_577_, 9, v_a_576_);
lean_closure_set(v___f_577_, 10, v_toPure_565_);
lean_closure_set(v___f_577_, 11, v_u_566_);
lean_closure_set(v___f_577_, 12, v_inst_567_);
lean_closure_set(v___f_577_, 13, v_toBind_568_);
lean_closure_set(v___f_577_, 14, v_kSuccess_569_);
lean_closure_set(v___f_577_, 15, v_inst_570_);
lean_closure_set(v___f_577_, 16, v_inst_571_);
lean_closure_set(v___f_577_, 17, v_P_x27_572_);
lean_closure_set(v___f_577_, 18, v_kFail_573_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1));
v___x_579_ = l_Lean_mkConst(v___x_578_, v___x_574_);
v___x_580_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_580_, 0, v___x_579_);
lean_closure_set(v___x_580_, 1, v_00_u03c6_564_);
v___x_581_ = lean_apply_2(v_inst_567_, lean_box(0), v___x_580_);
v___x_582_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_581_, v___f_577_);
return v___x_582_;
}
else
{
lean_dec(v_____do__lift_575_);
lean_dec(v___x_574_);
lean_dec_ref(v_P_x27_572_);
lean_dec_ref(v_inst_571_);
lean_dec_ref(v_inst_570_);
lean_dec(v_kSuccess_569_);
lean_dec(v_toBind_568_);
lean_dec(v_inst_567_);
lean_dec(v_u_566_);
lean_dec(v_toPure_565_);
lean_dec_ref(v_00_u03c6_564_);
lean_dec_ref(v_target_563_);
lean_dec_ref(v_hyps_562_);
lean_dec_ref(v_00_u03c3s_561_);
lean_dec(v___x_560_);
lean_dec_ref(v___x_559_);
lean_dec_ref(v___x_558_);
lean_dec_ref(v___x_557_);
lean_dec_ref(v___x_556_);
return v_kFail_573_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_556_ = stack[0].m_obj;
lean_object* v___x_557_ = stack[1].m_obj;
lean_object* v___x_558_ = stack[2].m_obj;
lean_object* v___x_559_ = stack[3].m_obj;
lean_object* v___x_560_ = stack[4].m_obj;
lean_object* v_00_u03c3s_561_ = stack[5].m_obj;
lean_object* v_hyps_562_ = stack[6].m_obj;
lean_object* v_target_563_ = stack[7].m_obj;
lean_object* v_00_u03c6_564_ = stack[8].m_obj;
lean_object* v_toPure_565_ = stack[9].m_obj;
lean_object* v_u_566_ = stack[10].m_obj;
lean_object* v_inst_567_ = stack[11].m_obj;
lean_object* v_toBind_568_ = stack[12].m_obj;
lean_object* v_kSuccess_569_ = stack[13].m_obj;
lean_object* v_inst_570_ = stack[14].m_obj;
lean_object* v_inst_571_ = stack[15].m_obj;
lean_object* v_P_x27_572_ = stack[16].m_obj;
lean_object* v_kFail_573_ = stack[17].m_obj;
lean_object* v___x_574_ = stack[18].m_obj;
lean_object* v_____do__lift_575_ = stack[19].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(v___x_556_, v___x_557_, v___x_558_, v___x_559_, v___x_560_, v_00_u03c3s_561_, v_hyps_562_, v_target_563_, v_00_u03c6_564_, v_toPure_565_, v_u_566_, v_inst_567_, v_toBind_568_, v_kSuccess_569_, v_inst_570_, v_inst_571_, v_P_x27_572_, v_kFail_573_, v___x_574_, v_____do__lift_575_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v___x_584_ = _args[0];
lean_object* v___x_585_ = _args[1];
lean_object* v___x_586_ = _args[2];
lean_object* v___x_587_ = _args[3];
lean_object* v___x_588_ = _args[4];
lean_object* v_00_u03c3s_589_ = _args[5];
lean_object* v_hyps_590_ = _args[6];
lean_object* v_target_591_ = _args[7];
lean_object* v_00_u03c6_592_ = _args[8];
lean_object* v_toPure_593_ = _args[9];
lean_object* v_u_594_ = _args[10];
lean_object* v_inst_595_ = _args[11];
lean_object* v_toBind_596_ = _args[12];
lean_object* v_kSuccess_597_ = _args[13];
lean_object* v_inst_598_ = _args[14];
lean_object* v_inst_599_ = _args[15];
lean_object* v_P_x27_600_ = _args[16];
lean_object* v_kFail_601_ = _args[17];
lean_object* v___x_602_ = _args[18];
lean_object* v_____do__lift_603_ = _args[19];
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v_00_u03c3s_589_, v_hyps_590_, v_target_591_, v_00_u03c6_592_, v_toPure_593_, v_u_594_, v_inst_595_, v_toBind_596_, v_kSuccess_597_, v_inst_598_, v_inst_599_, v_P_x27_600_, v_kFail_601_, v___x_602_, v_____do__lift_603_);
return v_res_604_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v_00_u03c3s_611_, lean_object* v_hyps_612_, lean_object* v_target_613_, lean_object* v_00_u03c6_614_, lean_object* v_toPure_615_, lean_object* v_u_616_, lean_object* v_inst_617_, lean_object* v_toBind_618_, lean_object* v_kSuccess_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_kFail_622_, lean_object* v___x_623_, lean_object* v_P_x27_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
lean_inc_ref(v_P_x27_624_);
lean_inc(v_toBind_618_);
lean_inc(v_inst_617_);
lean_inc_ref(v_00_u03c6_614_);
lean_inc_ref(v_hyps_612_);
lean_inc_ref(v_00_u03c3s_611_);
lean_inc(v___x_610_);
lean_inc_ref(v___x_609_);
lean_inc_ref(v___x_608_);
lean_inc_ref(v___x_607_);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed), 20, 19);
lean_closure_set(v___f_626_, 0, v___x_607_);
lean_closure_set(v___f_626_, 1, v___x_608_);
lean_closure_set(v___f_626_, 2, v___x_609_);
lean_closure_set(v___f_626_, 3, v___x_625_);
lean_closure_set(v___f_626_, 4, v___x_610_);
lean_closure_set(v___f_626_, 5, v_00_u03c3s_611_);
lean_closure_set(v___f_626_, 6, v_hyps_612_);
lean_closure_set(v___f_626_, 7, v_target_613_);
lean_closure_set(v___f_626_, 8, v_00_u03c6_614_);
lean_closure_set(v___f_626_, 9, v_toPure_615_);
lean_closure_set(v___f_626_, 10, v_u_616_);
lean_closure_set(v___f_626_, 11, v_inst_617_);
lean_closure_set(v___f_626_, 12, v_toBind_618_);
lean_closure_set(v___f_626_, 13, v_kSuccess_619_);
lean_closure_set(v___f_626_, 14, v_inst_620_);
lean_closure_set(v___f_626_, 15, v_inst_621_);
lean_closure_set(v___f_626_, 16, v_P_x27_624_);
lean_closure_set(v___f_626_, 17, v_kFail_622_);
lean_closure_set(v___f_626_, 18, v___x_623_);
v___x_627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1));
v___x_628_ = l_Lean_Name_mkStr5(v___x_607_, v___x_608_, v___x_609_, v___x_625_, v___x_627_);
v___x_629_ = l_Lean_mkConst(v___x_628_, v___x_610_);
v___x_630_ = l_Lean_mkApp4(v___x_629_, v_00_u03c3s_611_, v_hyps_612_, v_P_x27_624_, v_00_u03c6_614_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_closure((void*)(l_Lean_Meta_trySynthInstance___boxed), 7, 2);
lean_closure_set(v___x_632_, 0, v___x_630_);
lean_closure_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_apply_2(v_inst_617_, lean_box(0), v___x_632_);
v___x_634_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_633_, v___f_626_);
return v___x_634_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_607_ = stack[0].m_obj;
lean_object* v___x_608_ = stack[1].m_obj;
lean_object* v___x_609_ = stack[2].m_obj;
lean_object* v___x_610_ = stack[3].m_obj;
lean_object* v_00_u03c3s_611_ = stack[4].m_obj;
lean_object* v_hyps_612_ = stack[5].m_obj;
lean_object* v_target_613_ = stack[6].m_obj;
lean_object* v_00_u03c6_614_ = stack[7].m_obj;
lean_object* v_toPure_615_ = stack[8].m_obj;
lean_object* v_u_616_ = stack[9].m_obj;
lean_object* v_inst_617_ = stack[10].m_obj;
lean_object* v_toBind_618_ = stack[11].m_obj;
lean_object* v_kSuccess_619_ = stack[12].m_obj;
lean_object* v_inst_620_ = stack[13].m_obj;
lean_object* v_inst_621_ = stack[14].m_obj;
lean_object* v_kFail_622_ = stack[15].m_obj;
lean_object* v___x_623_ = stack[16].m_obj;
lean_object* v_P_x27_624_ = stack[17].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(v___x_607_, v___x_608_, v___x_609_, v___x_610_, v_00_u03c3s_611_, v_hyps_612_, v_target_613_, v_00_u03c6_614_, v_toPure_615_, v_u_616_, v_inst_617_, v_toBind_618_, v_kSuccess_619_, v_inst_620_, v_inst_621_, v_kFail_622_, v___x_623_, v_P_x27_624_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed(lean_object** _args){
lean_object* v___x_636_ = _args[0];
lean_object* v___x_637_ = _args[1];
lean_object* v___x_638_ = _args[2];
lean_object* v___x_639_ = _args[3];
lean_object* v_00_u03c3s_640_ = _args[4];
lean_object* v_hyps_641_ = _args[5];
lean_object* v_target_642_ = _args[6];
lean_object* v_00_u03c6_643_ = _args[7];
lean_object* v_toPure_644_ = _args[8];
lean_object* v_u_645_ = _args[9];
lean_object* v_inst_646_ = _args[10];
lean_object* v_toBind_647_ = _args[11];
lean_object* v_kSuccess_648_ = _args[12];
lean_object* v_inst_649_ = _args[13];
lean_object* v_inst_650_ = _args[14];
lean_object* v_kFail_651_ = _args[15];
lean_object* v___x_652_ = _args[16];
lean_object* v_P_x27_653_ = _args[17];
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(v___x_636_, v___x_637_, v___x_638_, v___x_639_, v_00_u03c3s_640_, v_hyps_641_, v_target_642_, v_00_u03c6_643_, v_toPure_644_, v_u_645_, v_inst_646_, v_toBind_647_, v_kSuccess_648_, v_inst_649_, v_inst_650_, v_kFail_651_, v___x_652_, v_P_x27_653_);
return v_res_654_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(lean_object* v_u_662_, lean_object* v_00_u03c3s_663_, lean_object* v_hyps_664_, lean_object* v_target_665_, lean_object* v_toPure_666_, lean_object* v_inst_667_, lean_object* v_toBind_668_, lean_object* v_kSuccess_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_kFail_672_, uint8_t v___x_673_, lean_object* v___x_674_, lean_object* v_00_u03c6_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0));
v___x_677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1));
v___x_678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2));
v___x_679_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3));
v___x_680_ = lean_box(0);
lean_inc(v_u_662_);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v_u_662_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_inc(v_toBind_668_);
lean_inc(v_inst_667_);
lean_inc_ref(v_00_u03c3s_663_);
lean_inc_ref(v___x_681_);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed), 18, 17);
lean_closure_set(v___f_682_, 0, v___x_676_);
lean_closure_set(v___f_682_, 1, v___x_677_);
lean_closure_set(v___f_682_, 2, v___x_678_);
lean_closure_set(v___f_682_, 3, v___x_681_);
lean_closure_set(v___f_682_, 4, v_00_u03c3s_663_);
lean_closure_set(v___f_682_, 5, v_hyps_664_);
lean_closure_set(v___f_682_, 6, v_target_665_);
lean_closure_set(v___f_682_, 7, v_00_u03c6_675_);
lean_closure_set(v___f_682_, 8, v_toPure_666_);
lean_closure_set(v___f_682_, 9, v_u_662_);
lean_closure_set(v___f_682_, 10, v_inst_667_);
lean_closure_set(v___f_682_, 11, v_toBind_668_);
lean_closure_set(v___f_682_, 12, v_kSuccess_669_);
lean_closure_set(v___f_682_, 13, v_inst_670_);
lean_closure_set(v___f_682_, 14, v_inst_671_);
lean_closure_set(v___f_682_, 15, v_kFail_672_);
lean_closure_set(v___f_682_, 16, v___x_680_);
v___x_683_ = l_Lean_mkConst(v___x_679_, v___x_681_);
v___x_684_ = l_Lean_Expr_app___override(v___x_683_, v_00_u03c3s_663_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
v___x_686_ = lean_box(v___x_673_);
v___x_687_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_687_, 0, v___x_685_);
lean_closure_set(v___x_687_, 1, v___x_686_);
lean_closure_set(v___x_687_, 2, v___x_674_);
v___x_688_ = lean_apply_2(v_inst_667_, lean_box(0), v___x_687_);
v___x_689_ = lean_apply_4(v_toBind_668_, lean_box(0), lean_box(0), v___x_688_, v___f_682_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_662_ = stack[0].m_obj;
lean_object* v_00_u03c3s_663_ = stack[1].m_obj;
lean_object* v_hyps_664_ = stack[2].m_obj;
lean_object* v_target_665_ = stack[3].m_obj;
lean_object* v_toPure_666_ = stack[4].m_obj;
lean_object* v_inst_667_ = stack[5].m_obj;
lean_object* v_toBind_668_ = stack[6].m_obj;
lean_object* v_kSuccess_669_ = stack[7].m_obj;
lean_object* v_inst_670_ = stack[8].m_obj;
lean_object* v_inst_671_ = stack[9].m_obj;
lean_object* v_kFail_672_ = stack[10].m_obj;
uint8_t v___x_673_ = stack[11].m_num;
lean_object* v___x_674_ = stack[12].m_obj;
lean_object* v_00_u03c6_675_ = stack[13].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(v_u_662_, v_00_u03c3s_663_, v_hyps_664_, v_target_665_, v_toPure_666_, v_inst_667_, v_toBind_668_, v_kSuccess_669_, v_inst_670_, v_inst_671_, v_kFail_672_, v___x_673_, v___x_674_, v_00_u03c6_675_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed(lean_object* v_u_691_, lean_object* v_00_u03c3s_692_, lean_object* v_hyps_693_, lean_object* v_target_694_, lean_object* v_toPure_695_, lean_object* v_inst_696_, lean_object* v_toBind_697_, lean_object* v_kSuccess_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_kFail_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v_00_u03c6_704_){
_start:
{
uint8_t v___x_883__boxed_705_; lean_object* v_res_706_; 
v___x_883__boxed_705_ = lean_unbox(v___x_702_);
v_res_706_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(v_u_691_, v_00_u03c3s_692_, v_hyps_693_, v_target_694_, v_toPure_695_, v_inst_696_, v_toBind_697_, v_kSuccess_698_, v_inst_699_, v_inst_700_, v_kFail_701_, v___x_883__boxed_705_, v___x_703_, v_00_u03c6_704_);
return v_res_706_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_mkSort(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2(void){
_start:
{
lean_object* v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_711_ = lean_box(0);
v___x_712_ = 0;
v___x_713_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1);
v___x_714_ = lean_box(v___x_712_);
v___x_715_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_715_, 0, v___x_713_);
lean_closure_set(v___x_715_, 1, v___x_714_);
lean_closure_set(v___x_715_, 2, v___x_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_goal_719_, lean_object* v_kFail_720_, lean_object* v_kSuccess_721_){
_start:
{
lean_object* v_toApplicative_722_; lean_object* v_u_723_; lean_object* v_00_u03c3s_724_; lean_object* v_hyps_725_; lean_object* v_target_726_; lean_object* v_toBind_727_; lean_object* v_toPure_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; 
v_toApplicative_722_ = lean_ctor_get(v_inst_716_, 0);
v_u_723_ = lean_ctor_get(v_goal_719_, 0);
lean_inc(v_u_723_);
v_00_u03c3s_724_ = lean_ctor_get(v_goal_719_, 1);
lean_inc_ref(v_00_u03c3s_724_);
v_hyps_725_ = lean_ctor_get(v_goal_719_, 2);
lean_inc_ref(v_hyps_725_);
v_target_726_ = lean_ctor_get(v_goal_719_, 3);
lean_inc_ref(v_target_726_);
lean_dec_ref(v_goal_719_);
v_toBind_727_ = lean_ctor_get(v_inst_716_, 1);
lean_inc_n(v_toBind_727_, 2);
v_toPure_728_ = lean_ctor_get(v_toApplicative_722_, 1);
lean_inc(v_toPure_728_);
v___x_729_ = 0;
v___x_730_ = lean_box(0);
v___x_731_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2);
lean_inc(v_inst_718_);
v___x_732_ = lean_apply_2(v_inst_718_, lean_box(0), v___x_731_);
v___x_733_ = lean_box(v___x_729_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_734_, 0, v_u_723_);
lean_closure_set(v___f_734_, 1, v_00_u03c3s_724_);
lean_closure_set(v___f_734_, 2, v_hyps_725_);
lean_closure_set(v___f_734_, 3, v_target_726_);
lean_closure_set(v___f_734_, 4, v_toPure_728_);
lean_closure_set(v___f_734_, 5, v_inst_718_);
lean_closure_set(v___f_734_, 6, v_toBind_727_);
lean_closure_set(v___f_734_, 7, v_kSuccess_721_);
lean_closure_set(v___f_734_, 8, v_inst_717_);
lean_closure_set(v___f_734_, 9, v_inst_716_);
lean_closure_set(v___f_734_, 10, v_kFail_720_);
lean_closure_set(v___f_734_, 11, v___x_733_);
lean_closure_set(v___f_734_, 12, v___x_730_);
v___x_735_ = lean_apply_4(v_toBind_727_, lean_box(0), lean_box(0), v___x_732_, v___f_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore(lean_object* v_m_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_goal_740_, lean_object* v_kFail_741_, lean_object* v_kSuccess_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_737_, v_inst_738_, v_inst_739_, v_goal_740_, v_kFail_741_, v_kSuccess_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(lean_object* v_k_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_goal_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_apply_1(v_k_744_, v_goal_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed(lean_object* v_k_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_goal_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(v_k_749_, v_x_750_, v_x_751_, v_goal_752_);
lean_dec_ref(v_x_751_);
lean_dec_ref(v_x_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_goal_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_inc(v_k_758_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_759_, 0, v_k_758_);
lean_inc_ref(v_goal_757_);
v___x_760_ = lean_apply_1(v_k_758_, v_goal_757_);
v___x_761_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_754_, v_inst_755_, v_inst_756_, v_goal_757_, v___x_760_, v___f_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame(lean_object* v_m_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_goal_766_, lean_object* v_k_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(v_inst_763_, v_inst_764_, v_inst_765_, v_goal_766_, v_k_767_);
return v___x_768_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(lean_object* v_e_769_, lean_object* v___y_770_){
_start:
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_Expr_hasMVar(v_e_769_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_e_769_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; lean_object* v_mctx_775_; lean_object* v___x_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_779_; lean_object* v_cache_780_; lean_object* v_zetaDeltaFVarIds_781_; lean_object* v_postponed_782_; lean_object* v_diag_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_792_; 
v___x_774_ = lean_st_ref_get(v___y_770_);
v_mctx_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_mctx_775_);
lean_dec(v___x_774_);
v___x_776_ = l_Lean_instantiateMVarsCore(v_mctx_775_, v_e_769_);
v_fst_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_fst_777_);
v_snd_778_ = lean_ctor_get(v___x_776_, 1);
lean_inc(v_snd_778_);
lean_dec_ref(v___x_776_);
v___x_779_ = lean_st_ref_take(v___y_770_);
v_cache_780_ = lean_ctor_get(v___x_779_, 1);
v_zetaDeltaFVarIds_781_ = lean_ctor_get(v___x_779_, 2);
v_postponed_782_ = lean_ctor_get(v___x_779_, 3);
v_diag_783_ = lean_ctor_get(v___x_779_, 4);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_793_);
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_diag_783_);
lean_inc(v_postponed_782_);
lean_inc(v_zetaDeltaFVarIds_781_);
lean_inc(v_cache_780_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_snd_778_);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_snd_778_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_cache_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_zetaDeltaFVarIds_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_postponed_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_diag_783_);
v___x_788_ = v_reuseFailAlloc_791_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_st_ref_put(v___y_770_, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v_fst_777_);
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_769_ = stack[0].m_obj;
lean_object* v___y_770_ = stack[1].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_769_, v___y_770_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg___boxed(lean_object* v_e_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_795_, v___y_796_);
lean_dec(v___y_796_);
return v_res_798_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(lean_object* v_e_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_799_, v___y_805_);
return v___x_809_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_799_ = stack[0].m_obj;
lean_object* v___y_800_ = stack[1].m_obj;
lean_object* v___y_801_ = stack[2].m_obj;
lean_object* v___y_802_ = stack[3].m_obj;
lean_object* v___y_803_ = stack[4].m_obj;
lean_object* v___y_804_ = stack[5].m_obj;
lean_object* v___y_805_ = stack[6].m_obj;
lean_object* v___y_806_ = stack[7].m_obj;
lean_object* v___y_807_ = stack[8].m_obj;
lean_object* v_res_810_;
v_res_810_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(v_e_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___boxed(lean_object* v_e_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(v_e_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_821_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v___x_832_ = lean_apply_9(v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, lean_box(0));
return v___x_832_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_822_ = stack[0].m_obj;
lean_object* v___y_823_ = stack[1].m_obj;
lean_object* v___y_824_ = stack[2].m_obj;
lean_object* v___y_825_ = stack[3].m_obj;
lean_object* v___y_826_ = stack[4].m_obj;
lean_object* v___y_827_ = stack[5].m_obj;
lean_object* v___y_828_ = stack[6].m_obj;
lean_object* v___y_829_ = stack[7].m_obj;
lean_object* v___y_830_ = stack[8].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed(lean_object* v_x_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(v_x_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_844_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(lean_object* v_mvarId_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; 
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_856_, 0, v_x_846_);
lean_closure_set(v___f_856_, 1, v___y_847_);
lean_closure_set(v___f_856_, 2, v___y_848_);
lean_closure_set(v___f_856_, 3, v___y_849_);
lean_closure_set(v___f_856_, 4, v___y_850_);
v___x_857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_845_, v___f_856_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_845_ = stack[0].m_obj;
lean_object* v_x_846_ = stack[1].m_obj;
lean_object* v___y_847_ = stack[2].m_obj;
lean_object* v___y_848_ = stack[3].m_obj;
lean_object* v___y_849_ = stack[4].m_obj;
lean_object* v___y_850_ = stack[5].m_obj;
lean_object* v___y_851_ = stack[6].m_obj;
lean_object* v___y_852_ = stack[7].m_obj;
lean_object* v___y_853_ = stack[8].m_obj;
lean_object* v___y_854_ = stack[9].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___boxed(lean_object* v_mvarId_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_878_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(lean_object* v_00_u03b1_879_, lean_object* v_mvarId_880_, lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_880_, v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_880_ = stack[1].m_obj;
lean_object* v_x_881_ = stack[2].m_obj;
lean_object* v___y_882_ = stack[3].m_obj;
lean_object* v___y_883_ = stack[4].m_obj;
lean_object* v___y_884_ = stack[5].m_obj;
lean_object* v___y_885_ = stack[6].m_obj;
lean_object* v___y_886_ = stack[7].m_obj;
lean_object* v___y_887_ = stack[8].m_obj;
lean_object* v___y_888_ = stack[9].m_obj;
lean_object* v___y_889_ = stack[10].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(lean_box(0), v_mvarId_880_, v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___boxed(lean_object* v_00_u03b1_893_, lean_object* v_mvarId_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(v_00_u03b1_893_, v_mvarId_894_, v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_905_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(lean_object* v_msgData_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_env_913_; uint8_t v___x_914_; lean_object* v_env_915_; lean_object* v___x_916_; lean_object* v_toCold_917_; lean_object* v_mctx_918_; lean_object* v_lctx_919_; lean_object* v_options_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_912_ = lean_st_ref_get(v___y_910_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
v___x_914_ = 0;
v_env_915_ = l_Lean_Environment_setRecordingDeps(v_env_913_, v___x_914_);
v___x_916_ = lean_st_ref_get(v___y_908_);
v_toCold_917_ = lean_ctor_get(v___y_909_, 0);
v_mctx_918_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_mctx_918_);
lean_dec(v___x_916_);
v_lctx_919_ = lean_ctor_get(v___y_907_, 2);
v_options_920_ = lean_ctor_get(v_toCold_917_, 2);
lean_inc_ref(v_options_920_);
lean_inc_ref(v_lctx_919_);
v___x_921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_921_, 0, v_env_915_);
lean_ctor_set(v___x_921_, 1, v_mctx_918_);
lean_ctor_set(v___x_921_, 2, v_lctx_919_);
lean_ctor_set(v___x_921_, 3, v_options_920_);
v___x_922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_msgData_906_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_906_ = stack[0].m_obj;
lean_object* v___y_907_ = stack[1].m_obj;
lean_object* v___y_908_ = stack[2].m_obj;
lean_object* v___y_909_ = stack[3].m_obj;
lean_object* v___y_910_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msgData_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0___boxed(lean_object* v_msgData_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msgData_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_ref_938_; lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_ref_938_ = lean_ctor_get(v___y_935_, 2);
v___x_939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc(v_ref_938_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_ref_938_);
lean_ctor_set(v___x_944_, 1, v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_932_ = stack[0].m_obj;
lean_object* v___y_933_ = stack[1].m_obj;
lean_object* v___y_934_ = stack[2].m_obj;
lean_object* v___y_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg___boxed(lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1);
v___x_970_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v___x_969_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_970_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_960_ = stack[0].m_obj;
lean_object* v___y_961_ = stack[1].m_obj;
lean_object* v___y_962_ = stack[2].m_obj;
lean_object* v___y_963_ = stack[3].m_obj;
lean_object* v___y_964_ = stack[4].m_obj;
lean_object* v___y_965_ = stack[5].m_obj;
lean_object* v___y_966_ = stack[6].m_obj;
lean_object* v___y_967_ = stack[7].m_obj;
lean_object* v_res_971_;
v_res_971_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed(lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v_x_972_);
return v_res_981_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_goal_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_984_);
v___x_995_ = lean_box(0);
v___x_996_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_994_, v___x_995_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = l_Lean_Expr_mvarId_x21(v_a_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1000_, v___y_986_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v___x_1001_, 0);
lean_dec(v_unused_1009_);
v___x_1003_ = v___x_1001_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v___x_1001_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_a_997_);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_997_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_997_);
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
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
return v___x_996_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_982_ = stack[0].m_obj;
lean_object* v_x_983_ = stack[1].m_obj;
lean_object* v_goal_984_ = stack[2].m_obj;
lean_object* v___y_985_ = stack[3].m_obj;
lean_object* v___y_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v___y_988_ = stack[6].m_obj;
lean_object* v___y_989_ = stack[7].m_obj;
lean_object* v___y_990_ = stack[8].m_obj;
lean_object* v___y_991_ = stack[9].m_obj;
lean_object* v___y_992_ = stack[10].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(v_x_982_, v_x_983_, v_goal_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed(lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_goal_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(v_x_1019_, v_x_1020_, v_goal_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_x_1020_);
lean_dec_ref(v_x_1019_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_ks_1036_; lean_object* v_vs_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1061_; 
v_ks_1036_ = lean_ctor_get(v_x_1032_, 0);
v_vs_1037_ = lean_ctor_get(v_x_1032_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1032_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1039_ = v_x_1032_;
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_vs_1037_);
lean_inc(v_ks_1036_);
lean_dec(v_x_1032_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_array_get_size(v_ks_1036_);
v___x_1042_ = lean_nat_dec_lt(v_x_1033_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v_x_1033_);
v___x_1043_ = lean_array_push(v_ks_1036_, v_x_1034_);
v___x_1044_ = lean_array_push(v_vs_1037_, v_x_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___x_1044_);
lean_ctor_set(v___x_1039_, 0, v___x_1043_);
v___x_1046_ = v___x_1039_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v_k_x27_1048_; uint8_t v___x_1049_; 
v_k_x27_1048_ = lean_array_fget_borrowed(v_ks_1036_, v_x_1033_);
v___x_1049_ = l_Lean_instBEqMVarId_beq(v_x_1034_, v_k_x27_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1051_; 
if (v_isShared_1040_ == 0)
{
v___x_1051_ = v___x_1039_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_ks_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_vs_1037_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_x_1033_, v___x_1052_);
lean_dec(v_x_1033_);
v_x_1032_ = v___x_1051_;
v_x_1033_ = v___x_1053_;
goto _start;
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = lean_array_fset(v_ks_1036_, v_x_1033_, v_x_1034_);
v___x_1057_ = lean_array_fset(v_vs_1037_, v_x_1033_, v_x_1035_);
lean_dec(v_x_1033_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___x_1057_);
lean_ctor_set(v___x_1039_, 0, v___x_1056_);
v___x_1059_ = v___x_1039_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_n_1062_, lean_object* v_k_1063_, lean_object* v_v_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_n_1062_, v___x_1065_, v_k_1063_, v_v_1064_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1067_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(lean_object* v_x_1068_, size_t v_x_1069_, size_t v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
lean_object* v_es_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v_j_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_es_1073_ = lean_ctor_get(v_x_1068_, 0);
v___x_1074_ = ((size_t)31ULL);
v___x_1075_ = lean_usize_land(v_x_1069_, v___x_1074_);
v_j_1076_ = lean_usize_to_nat(v___x_1075_);
v___x_1077_ = lean_array_get_size(v_es_1073_);
v___x_1078_ = lean_nat_dec_lt(v_j_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec(v_j_1076_);
lean_dec(v_x_1072_);
lean_dec(v_x_1071_);
return v_x_1068_;
}
else
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1117_; 
lean_inc_ref(v_es_1073_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_x_1068_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_x_1068_, 0);
lean_dec(v_unused_1118_);
v___x_1080_ = v_x_1068_;
v_isShared_1081_ = v_isSharedCheck_1117_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_x_1068_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1117_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_v_1082_; lean_object* v___x_1083_; lean_object* v_xs_x27_1084_; lean_object* v___y_1086_; 
v_v_1082_ = lean_array_fget(v_es_1073_, v_j_1076_);
v___x_1083_ = lean_box(0);
v_xs_x27_1084_ = lean_array_fset(v_es_1073_, v_j_1076_, v___x_1083_);
switch(lean_obj_tag(v_v_1082_))
{
case 0:
{
lean_object* v_key_1091_; lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_key_1091_ = lean_ctor_get(v_v_1082_, 0);
v_val_1092_ = lean_ctor_get(v_v_1082_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_v_1082_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1094_ = v_v_1082_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_inc(v_key_1091_);
lean_dec(v_v_1082_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_instBEqMVarId_beq(v_x_1071_, v_key_1091_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1094_);
v___x_1097_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1091_, v_val_1092_, v_x_1071_, v_x_1072_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___y_1086_ = v___x_1098_;
goto v___jp_1085_;
}
else
{
lean_object* v___x_1100_; 
lean_dec(v_val_1092_);
lean_dec(v_key_1091_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_x_1072_);
lean_ctor_set(v___x_1094_, 0, v_x_1071_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_x_1071_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_x_1072_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v___y_1086_ = v___x_1100_;
goto v___jp_1085_;
}
}
}
}
case 1:
{
lean_object* v_node_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1115_; 
v_node_1103_ = lean_ctor_get(v_v_1082_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_v_1082_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1105_ = v_v_1082_;
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_node_1103_);
lean_dec(v_v_1082_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1107_ = ((size_t)5ULL);
v___x_1108_ = lean_usize_shift_right(v_x_1069_, v___x_1107_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_add(v_x_1070_, v___x_1109_);
v___x_1111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_node_1103_, v___x_1108_, v___x_1110_, v_x_1071_, v_x_1072_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1111_);
v___x_1113_ = v___x_1105_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1086_ = v___x_1113_;
goto v___jp_1085_;
}
}
}
default: 
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_x_1071_);
lean_ctor_set(v___x_1116_, 1, v_x_1072_);
v___y_1086_ = v___x_1116_;
goto v___jp_1085_;
}
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_array_fset(v_xs_x27_1084_, v_j_1076_, v___y_1086_);
lean_dec(v_j_1076_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1087_);
v___x_1089_ = v___x_1080_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
else
{
lean_object* v_ks_1119_; lean_object* v_vs_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1138_; 
v_ks_1119_ = lean_ctor_get(v_x_1068_, 0);
v_vs_1120_ = lean_ctor_get(v_x_1068_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1068_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1122_ = v_x_1068_;
v_isShared_1123_ = v_isSharedCheck_1138_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_vs_1120_);
lean_inc(v_ks_1119_);
lean_dec(v_x_1068_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1138_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_ks_1119_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_vs_1120_);
v___x_1125_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v_newNode_1126_; size_t v___x_1127_; uint8_t v___x_1128_; 
v_newNode_1126_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v___x_1125_, v_x_1071_, v_x_1072_);
v___x_1127_ = ((size_t)7ULL);
v___x_1128_ = lean_usize_dec_le(v___x_1127_, v_x_1070_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1126_);
v___x_1130_ = lean_unsigned_to_nat(4u);
v___x_1131_ = lean_nat_dec_lt(v___x_1129_, v___x_1130_);
lean_dec(v___x_1129_);
if (v___x_1131_ == 0)
{
lean_object* v_ks_1132_; lean_object* v_vs_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_ks_1132_ = lean_ctor_get(v_newNode_1126_, 0);
lean_inc_ref(v_ks_1132_);
v_vs_1133_ = lean_ctor_get(v_newNode_1126_, 1);
lean_inc_ref(v_vs_1133_);
lean_dec_ref(v_newNode_1126_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_1136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_x_1070_, v_ks_1132_, v_vs_1133_, v___x_1134_, v___x_1135_);
lean_dec_ref(v_vs_1133_);
lean_dec_ref(v_ks_1132_);
return v___x_1136_;
}
else
{
return v_newNode_1126_;
}
}
else
{
return v_newNode_1126_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1068_ = stack[0].m_obj;
size_t v_x_1069_ = stack[1].m_num;
size_t v_x_1070_ = stack[2].m_num;
lean_object* v_x_1071_ = stack[3].m_obj;
lean_object* v_x_1072_ = stack[4].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1068_, v_x_1069_, v_x_1070_, v_x_1071_, v_x_1072_);
stack->m_obj
 = v_res_1139_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(size_t v_depth_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_i_1143_, lean_object* v_entries_1144_){
_start:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_keys_1141_);
v___x_1146_ = lean_nat_dec_lt(v_i_1143_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec(v_i_1143_);
return v_entries_1144_;
}
else
{
lean_object* v_k_1147_; lean_object* v_v_1148_; uint64_t v___x_1149_; size_t v_h_1150_; size_t v___x_1151_; lean_object* v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v_h_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_k_1147_ = lean_array_fget_borrowed(v_keys_1141_, v_i_1143_);
v_v_1148_ = lean_array_fget_borrowed(v_vals_1142_, v_i_1143_);
v___x_1149_ = l_Lean_instHashableMVarId_hash(v_k_1147_);
v_h_1150_ = lean_uint64_to_usize(v___x_1149_);
v___x_1151_ = ((size_t)5ULL);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_sub(v_depth_1140_, v___x_1153_);
v___x_1155_ = lean_usize_mul(v___x_1151_, v___x_1154_);
v_h_1156_ = lean_usize_shift_right(v_h_1150_, v___x_1155_);
v___x_1157_ = lean_nat_add(v_i_1143_, v___x_1152_);
lean_dec(v_i_1143_);
lean_inc(v_v_1148_);
lean_inc(v_k_1147_);
v___x_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_entries_1144_, v_h_1156_, v_depth_1140_, v_k_1147_, v_v_1148_);
v_i_1143_ = v___x_1157_;
v_entries_1144_ = v___x_1158_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1140_ = stack[0].m_num;
lean_object* v_keys_1141_ = stack[1].m_obj;
lean_object* v_vals_1142_ = stack[2].m_obj;
lean_object* v_i_1143_ = stack[3].m_obj;
lean_object* v_entries_1144_ = stack[4].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_1140_, v_keys_1141_, v_vals_1142_, v_i_1143_, v_entries_1144_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_depth_1161_, lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_i_1164_, lean_object* v_entries_1165_){
_start:
{
size_t v_depth_boxed_1166_; lean_object* v_res_1167_; 
v_depth_boxed_1166_ = lean_unbox_usize(v_depth_1161_);
lean_dec(v_depth_1161_);
v_res_1167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_boxed_1166_, v_keys_1162_, v_vals_1163_, v_i_1164_, v_entries_1165_);
lean_dec_ref(v_vals_1163_);
lean_dec_ref(v_keys_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
size_t v_x_11188__boxed_1173_; size_t v_x_11189__boxed_1174_; lean_object* v_res_1175_; 
v_x_11188__boxed_1173_ = lean_unbox_usize(v_x_1169_);
lean_dec(v_x_1169_);
v_x_11189__boxed_1174_ = lean_unbox_usize(v_x_1170_);
lean_dec(v_x_1170_);
v_res_1175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1168_, v_x_11188__boxed_1173_, v_x_11189__boxed_1174_, v_x_1171_, v_x_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
uint64_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1179_ = l_Lean_instHashableMVarId_hash(v_x_1177_);
v___x_1180_ = lean_uint64_to_usize(v___x_1179_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1176_, v___x_1180_, v___x_1181_, v_x_1177_, v_x_1178_);
return v___x_1182_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(lean_object* v_mvarId_1183_, lean_object* v_val_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_mctx_1188_; lean_object* v_cache_1189_; lean_object* v_zetaDeltaFVarIds_1190_; lean_object* v_postponed_1191_; lean_object* v_diag_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1222_; 
v___x_1187_ = lean_st_ref_take(v___y_1185_);
v_mctx_1188_ = lean_ctor_get(v___x_1187_, 0);
v_cache_1189_ = lean_ctor_get(v___x_1187_, 1);
v_zetaDeltaFVarIds_1190_ = lean_ctor_get(v___x_1187_, 2);
v_postponed_1191_ = lean_ctor_get(v___x_1187_, 3);
v_diag_1192_ = lean_ctor_get(v___x_1187_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1194_ = v___x_1187_;
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_diag_1192_);
lean_inc(v_postponed_1191_);
lean_inc(v_zetaDeltaFVarIds_1190_);
lean_inc(v_cache_1189_);
lean_inc(v_mctx_1188_);
lean_dec(v___x_1187_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_depth_1196_; lean_object* v_levelAssignDepth_1197_; lean_object* v_lmvarCounter_1198_; lean_object* v_mvarCounter_1199_; lean_object* v_lDecls_1200_; lean_object* v_decls_1201_; lean_object* v_userNames_1202_; lean_object* v_lAssignment_1203_; lean_object* v_eAssignment_1204_; lean_object* v_dAssignment_1205_; lean_object* v_instanceTypedMVars_1206_; lean_object* v_synthNormMemo_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1221_; 
v_depth_1196_ = lean_ctor_get(v_mctx_1188_, 0);
v_levelAssignDepth_1197_ = lean_ctor_get(v_mctx_1188_, 1);
v_lmvarCounter_1198_ = lean_ctor_get(v_mctx_1188_, 2);
v_mvarCounter_1199_ = lean_ctor_get(v_mctx_1188_, 3);
v_lDecls_1200_ = lean_ctor_get(v_mctx_1188_, 4);
v_decls_1201_ = lean_ctor_get(v_mctx_1188_, 5);
v_userNames_1202_ = lean_ctor_get(v_mctx_1188_, 6);
v_lAssignment_1203_ = lean_ctor_get(v_mctx_1188_, 7);
v_eAssignment_1204_ = lean_ctor_get(v_mctx_1188_, 8);
v_dAssignment_1205_ = lean_ctor_get(v_mctx_1188_, 9);
v_instanceTypedMVars_1206_ = lean_ctor_get(v_mctx_1188_, 10);
v_synthNormMemo_1207_ = lean_ctor_get(v_mctx_1188_, 11);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_mctx_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1209_ = v_mctx_1188_;
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_synthNormMemo_1207_);
lean_inc(v_instanceTypedMVars_1206_);
lean_inc(v_dAssignment_1205_);
lean_inc(v_eAssignment_1204_);
lean_inc(v_lAssignment_1203_);
lean_inc(v_userNames_1202_);
lean_inc(v_decls_1201_);
lean_inc(v_lDecls_1200_);
lean_inc(v_mvarCounter_1199_);
lean_inc(v_lmvarCounter_1198_);
lean_inc(v_levelAssignDepth_1197_);
lean_inc(v_depth_1196_);
lean_dec(v_mctx_1188_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1221_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_eAssignment_1204_, v_mvarId_1183_, v_val_1184_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 8, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_depth_1196_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_levelAssignDepth_1197_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_lmvarCounter_1198_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_mvarCounter_1199_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_lDecls_1200_);
lean_ctor_set(v_reuseFailAlloc_1220_, 5, v_decls_1201_);
lean_ctor_set(v_reuseFailAlloc_1220_, 6, v_userNames_1202_);
lean_ctor_set(v_reuseFailAlloc_1220_, 7, v_lAssignment_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 8, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1220_, 9, v_dAssignment_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 10, v_instanceTypedMVars_1206_);
lean_ctor_set(v_reuseFailAlloc_1220_, 11, v_synthNormMemo_1207_);
v___x_1214_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1214_);
v___x_1216_ = v___x_1194_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_cache_1189_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_zetaDeltaFVarIds_1190_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_postponed_1191_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_diag_1192_);
v___x_1216_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_st_ref_put(v___y_1185_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1211_);
return v___x_1218_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1183_ = stack[0].m_obj;
lean_object* v_val_1184_ = stack[1].m_obj;
lean_object* v___y_1185_ = stack[2].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1183_, v_val_1184_, v___y_1185_);
stack->m_obj
 = v_res_1223_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg___boxed(lean_object* v_mvarId_1224_, lean_object* v_val_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1224_, v_val_1225_, v___y_1226_);
lean_dec(v___y_1226_);
return v_res_1228_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_ref_1235_; lean_object* v___x_1236_; lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_ref_1235_ = lean_ctor_get(v___y_1232_, 2);
v___x_1236_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_inc(v_ref_1235_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_ref_1235_);
lean_ctor_set(v___x_1241_, 1, v_a_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1229_ = stack[0].m_obj;
lean_object* v___y_1230_ = stack[1].m_obj;
lean_object* v___y_1231_ = stack[2].m_obj;
lean_object* v___y_1232_ = stack[3].m_obj;
lean_object* v___y_1233_ = stack[4].m_obj;
lean_object* v_res_1246_;
v_res_1246_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
stack->m_obj
 = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg___boxed(lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(lean_object* v_k_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1261_);
lean_inc_ref(v___y_1260_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1255_);
v___x_1265_ = lean_apply_10(v_k_1254_, v_b_1259_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, lean_box(0));
return v___x_1265_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1254_ = stack[0].m_obj;
lean_object* v___y_1255_ = stack[1].m_obj;
lean_object* v___y_1256_ = stack[2].m_obj;
lean_object* v___y_1257_ = stack[3].m_obj;
lean_object* v___y_1258_ = stack[4].m_obj;
lean_object* v_b_1259_ = stack[5].m_obj;
lean_object* v___y_1260_ = stack[6].m_obj;
lean_object* v___y_1261_ = stack[7].m_obj;
lean_object* v___y_1262_ = stack[8].m_obj;
lean_object* v___y_1263_ = stack[9].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(v_k_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v_b_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_k_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(v_k_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v_b_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1278_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(lean_object* v_name_1279_, uint8_t v_bi_1280_, lean_object* v_type_1281_, lean_object* v_k_1282_, uint8_t v_kind_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___f_1293_; lean_object* v___x_1294_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1293_, 0, v_k_1282_);
lean_closure_set(v___f_1293_, 1, v___y_1284_);
lean_closure_set(v___f_1293_, 2, v___y_1285_);
lean_closure_set(v___f_1293_, 3, v___y_1286_);
lean_closure_set(v___f_1293_, 4, v___y_1287_);
v___x_1294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1279_, v_bi_1280_, v_type_1281_, v___f_1293_, v_kind_1283_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1294_) == 0)
{
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1279_ = stack[0].m_obj;
uint8_t v_bi_1280_ = stack[1].m_num;
lean_object* v_type_1281_ = stack[2].m_obj;
lean_object* v_k_1282_ = stack[3].m_obj;
uint8_t v_kind_1283_ = stack[4].m_num;
lean_object* v___y_1284_ = stack[5].m_obj;
lean_object* v___y_1285_ = stack[6].m_obj;
lean_object* v___y_1286_ = stack[7].m_obj;
lean_object* v___y_1287_ = stack[8].m_obj;
lean_object* v___y_1288_ = stack[9].m_obj;
lean_object* v___y_1289_ = stack[10].m_obj;
lean_object* v___y_1290_ = stack[11].m_obj;
lean_object* v___y_1291_ = stack[12].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1279_, v_bi_1280_, v_type_1281_, v_k_1282_, v_kind_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_name_1304_, lean_object* v_bi_1305_, lean_object* v_type_1306_, lean_object* v_k_1307_, lean_object* v_kind_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_bi_boxed_1318_; uint8_t v_kind_boxed_1319_; lean_object* v_res_1320_; 
v_bi_boxed_1318_ = lean_unbox(v_bi_1305_);
v_kind_boxed_1319_ = lean_unbox(v_kind_1308_);
v_res_1320_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1304_, v_bi_boxed_1318_, v_type_1306_, v_k_1307_, v_kind_boxed_1319_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1320_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(lean_object* v_name_1321_, lean_object* v_type_1322_, lean_object* v_k_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = 0;
v___x_1334_ = 0;
v___x_1335_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1321_, v___x_1333_, v_type_1322_, v_k_1323_, v___x_1334_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1335_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1321_ = stack[0].m_obj;
lean_object* v_type_1322_ = stack[1].m_obj;
lean_object* v_k_1323_ = stack[2].m_obj;
lean_object* v___y_1324_ = stack[3].m_obj;
lean_object* v___y_1325_ = stack[4].m_obj;
lean_object* v___y_1326_ = stack[5].m_obj;
lean_object* v___y_1327_ = stack[6].m_obj;
lean_object* v___y_1328_ = stack[7].m_obj;
lean_object* v___y_1329_ = stack[8].m_obj;
lean_object* v___y_1330_ = stack[9].m_obj;
lean_object* v___y_1331_ = stack[10].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1321_, v_type_1322_, v_k_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg___boxed(lean_object* v_name_1337_, lean_object* v_type_1338_, lean_object* v_k_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1337_, v_type_1338_, v_k_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1349_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(lean_object* v_kSuccess_1350_, lean_object* v_a_1351_, lean_object* v_goal_1352_, uint8_t v_a_1353_, uint8_t v___x_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_00_u03c3s_1360_, lean_object* v_hyps_1361_, lean_object* v_a_1362_, lean_object* v_target_1363_, lean_object* v_a_1364_, lean_object* v_h_u03c6_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc_ref(v___y_1366_);
lean_inc_ref(v_h_u03c6_1365_);
lean_inc_ref(v_a_1351_);
v___x_1375_ = lean_apply_12(v_kSuccess_1350_, v_a_1351_, v_h_u03c6_1365_, v_goal_1352_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, lean_box(0));
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_mk_empty_array_with_capacity(v___x_1377_);
v___x_1379_ = lean_array_push(v___x_1378_, v_h_u03c6_1365_);
v___x_1380_ = 1;
v___x_1381_ = l_Lean_Meta_mkLambdaFVars(v___x_1379_, v_a_1376_, v_a_1353_, v___x_1354_, v_a_1353_, v___x_1354_, v___x_1380_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec_ref(v___x_1379_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1394_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_prf_1390_; lean_object* v___x_1392_; 
v___x_1386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_1388_ = l_Lean_Name_mkStr6(v___x_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1386_, v___x_1387_);
v___x_1389_ = l_Lean_mkConst(v___x_1388_, v___x_1359_);
v_prf_1390_ = l_Lean_mkApp7(v___x_1389_, v_00_u03c3s_1360_, v_hyps_1361_, v_a_1362_, v_target_1363_, v_a_1351_, v_a_1364_, v_a_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_prf_1390_);
v___x_1392_ = v___x_1384_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_prf_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_target_1363_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_hyps_1361_);
lean_dec_ref(v_00_u03c3s_1360_);
lean_dec(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_a_1351_);
return v___x_1381_;
}
}
else
{
lean_dec_ref(v_h_u03c6_1365_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_target_1363_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_hyps_1361_);
lean_dec_ref(v_00_u03c3s_1360_);
lean_dec(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v_a_1351_);
return v___x_1375_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kSuccess_1350_ = stack[0].m_obj;
lean_object* v_a_1351_ = stack[1].m_obj;
lean_object* v_goal_1352_ = stack[2].m_obj;
uint8_t v_a_1353_ = stack[3].m_num;
uint8_t v___x_1354_ = stack[4].m_num;
lean_object* v___x_1355_ = stack[5].m_obj;
lean_object* v___x_1356_ = stack[6].m_obj;
lean_object* v___x_1357_ = stack[7].m_obj;
lean_object* v___x_1358_ = stack[8].m_obj;
lean_object* v___x_1359_ = stack[9].m_obj;
lean_object* v_00_u03c3s_1360_ = stack[10].m_obj;
lean_object* v_hyps_1361_ = stack[11].m_obj;
lean_object* v_a_1362_ = stack[12].m_obj;
lean_object* v_target_1363_ = stack[13].m_obj;
lean_object* v_a_1364_ = stack[14].m_obj;
lean_object* v_h_u03c6_1365_ = stack[15].m_obj;
lean_object* v___y_1366_ = stack[16].m_obj;
lean_object* v___y_1367_ = stack[17].m_obj;
lean_object* v___y_1368_ = stack[18].m_obj;
lean_object* v___y_1369_ = stack[19].m_obj;
lean_object* v___y_1370_ = stack[20].m_obj;
lean_object* v___y_1371_ = stack[21].m_obj;
lean_object* v___y_1372_ = stack[22].m_obj;
lean_object* v___y_1373_ = stack[23].m_obj;
lean_object* v_res_1395_;
v_res_1395_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(v_kSuccess_1350_, v_a_1351_, v_goal_1352_, v_a_1353_, v___x_1354_, v___x_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1359_, v_00_u03c3s_1360_, v_hyps_1361_, v_a_1362_, v_target_1363_, v_a_1364_, v_h_u03c6_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
stack->m_obj
 = v_res_1395_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed(lean_object** _args){
lean_object* v_kSuccess_1396_ = _args[0];
lean_object* v_a_1397_ = _args[1];
lean_object* v_goal_1398_ = _args[2];
lean_object* v_a_1399_ = _args[3];
lean_object* v___x_1400_ = _args[4];
lean_object* v___x_1401_ = _args[5];
lean_object* v___x_1402_ = _args[6];
lean_object* v___x_1403_ = _args[7];
lean_object* v___x_1404_ = _args[8];
lean_object* v___x_1405_ = _args[9];
lean_object* v_00_u03c3s_1406_ = _args[10];
lean_object* v_hyps_1407_ = _args[11];
lean_object* v_a_1408_ = _args[12];
lean_object* v_target_1409_ = _args[13];
lean_object* v_a_1410_ = _args[14];
lean_object* v_h_u03c6_1411_ = _args[15];
lean_object* v___y_1412_ = _args[16];
lean_object* v___y_1413_ = _args[17];
lean_object* v___y_1414_ = _args[18];
lean_object* v___y_1415_ = _args[19];
lean_object* v___y_1416_ = _args[20];
lean_object* v___y_1417_ = _args[21];
lean_object* v___y_1418_ = _args[22];
lean_object* v___y_1419_ = _args[23];
lean_object* v___y_1420_ = _args[24];
_start:
{
uint8_t v_a_11748__boxed_1421_; uint8_t v___x_11749__boxed_1422_; lean_object* v_res_1423_; 
v_a_11748__boxed_1421_ = lean_unbox(v_a_1399_);
v___x_11749__boxed_1422_ = lean_unbox(v___x_1400_);
v_res_1423_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(v_kSuccess_1396_, v_a_1397_, v_goal_1398_, v_a_11748__boxed_1421_, v___x_11749__boxed_1422_, v___x_1401_, v___x_1402_, v___x_1403_, v___x_1404_, v___x_1405_, v_00_u03c3s_1406_, v_hyps_1407_, v_a_1408_, v_target_1409_, v_a_1410_, v_h_u03c6_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1));
v___x_1432_ = l_Lean_mkConst(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(lean_object* v_goal_1433_, lean_object* v_kFail_1434_, lean_object* v_kSuccess_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_u_1445_; lean_object* v_00_u03c3s_1446_; lean_object* v_hyps_1447_; lean_object* v_target_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1524_; 
v_u_1445_ = lean_ctor_get(v_goal_1433_, 0);
v_00_u03c3s_1446_ = lean_ctor_get(v_goal_1433_, 1);
v_hyps_1447_ = lean_ctor_get(v_goal_1433_, 2);
v_target_1448_ = lean_ctor_get(v_goal_1433_, 3);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_goal_1433_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1450_ = v_goal_1433_;
v_isShared_1451_ = v_isSharedCheck_1524_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_target_1448_);
lean_inc(v_hyps_1447_);
lean_inc(v_00_u03c3s_1446_);
lean_inc(v_u_1445_);
lean_dec(v_goal_1433_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1524_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1);
v___x_1453_ = 0;
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Lean_Meta_mkFreshExprMVar(v___x_1452_, v___x_1453_, v___x_1454_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1523_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1523_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1523_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0));
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1));
v___x_1462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2));
v___x_1463_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3));
v___x_1464_ = lean_box(0);
lean_inc(v_u_1445_);
v___x_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_u_1445_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_inc_ref(v___x_1465_);
v___x_1466_ = l_Lean_mkConst(v___x_1463_, v___x_1465_);
lean_inc_ref(v_00_u03c3s_1446_);
v___x_1467_ = l_Lean_Expr_app___override(v___x_1466_, v_00_u03c3s_1446_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1467_);
v___x_1469_ = v___x_1458_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_mkFreshExprMVar(v___x_1469_, v___x_1453_, v___x_1454_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_n(v_a_1471_, 2);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0));
lean_inc_ref(v___x_1465_);
v___x_1474_ = l_Lean_mkConst(v___x_1473_, v___x_1465_);
lean_inc(v_a_1456_);
lean_inc_ref(v_hyps_1447_);
lean_inc_ref(v_00_u03c3s_1446_);
v___x_1475_ = l_Lean_mkApp4(v___x_1474_, v_00_u03c3s_1446_, v_hyps_1447_, v_a_1471_, v_a_1456_);
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_Meta_trySynthInstance(v___x_1475_, v___x_1476_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
if (lean_obj_tag(v_a_1478_) == 1)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_a_1479_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v_a_1478_, 1);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1);
lean_inc(v_a_1456_);
v___x_1481_ = l_Lean_Meta_isExprDefEq(v___x_1480_, v_a_1456_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; uint8_t v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = lean_unbox(v_a_1482_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v_kFail_1434_);
v___x_1484_ = 1;
lean_inc_ref(v_hyps_1447_);
v___x_1485_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_hyps_1447_, v_a_1471_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v_goal_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_n(v_a_1486_, 2);
lean_dec_ref_known(v___x_1485_, 1);
lean_inc_ref(v_target_1448_);
lean_inc_ref(v_00_u03c3s_1446_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 2, v_a_1486_);
v_goal_1488_ = v___x_1450_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_u_1445_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_00_u03c3s_1446_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_a_1486_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_target_1448_);
v_goal_1488_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_box(v___x_1484_);
lean_inc(v_a_1456_);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed), 25, 15);
lean_closure_set(v___f_1490_, 0, v_kSuccess_1435_);
lean_closure_set(v___f_1490_, 1, v_a_1456_);
lean_closure_set(v___f_1490_, 2, v_goal_1488_);
lean_closure_set(v___f_1490_, 3, v_a_1482_);
lean_closure_set(v___f_1490_, 4, v___x_1489_);
lean_closure_set(v___f_1490_, 5, v___x_1460_);
lean_closure_set(v___f_1490_, 6, v___x_1461_);
lean_closure_set(v___f_1490_, 7, v___x_1462_);
lean_closure_set(v___f_1490_, 8, v___x_1472_);
lean_closure_set(v___f_1490_, 9, v___x_1465_);
lean_closure_set(v___f_1490_, 10, v_00_u03c3s_1446_);
lean_closure_set(v___f_1490_, 11, v_hyps_1447_);
lean_closure_set(v___f_1490_, 12, v_a_1486_);
lean_closure_set(v___f_1490_, 13, v_target_1448_);
lean_closure_set(v___f_1490_, 14, v_a_1479_);
v___x_1491_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_1492_ = l_Lean_Core_mkFreshUserName(v___x_1491_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_a_1493_, v_a_1456_, v___f_1490_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1494_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v___f_1490_);
lean_dec(v_a_1456_);
v_a_1495_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1492_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1492_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_dec(v_a_1482_);
lean_dec(v_a_1479_);
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
return v___x_1485_;
}
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_a_1482_);
lean_dec(v_a_1479_);
lean_dec(v_a_1471_);
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1504_ = lean_apply_9(v_kFail_1434_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, lean_box(0));
return v___x_1504_;
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1479_);
lean_dec(v_a_1471_);
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_dec_ref(v_kFail_1434_);
v_a_1505_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1481_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1481_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_a_1478_);
lean_dec(v_a_1471_);
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1513_ = lean_apply_9(v_kFail_1434_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, lean_box(0));
return v___x_1513_;
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1471_);
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_dec_ref(v_kFail_1434_);
v_a_1514_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1477_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1477_);
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
lean_dec_ref_known(v___x_1465_, 2);
lean_dec(v_a_1456_);
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_dec_ref(v_kFail_1434_);
return v___x_1470_;
}
}
}
}
else
{
lean_del_object(v___x_1450_);
lean_dec_ref(v_target_1448_);
lean_dec_ref(v_hyps_1447_);
lean_dec_ref(v_00_u03c3s_1446_);
lean_dec(v_u_1445_);
lean_dec_ref(v_kSuccess_1435_);
lean_dec_ref(v_kFail_1434_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1433_ = stack[0].m_obj;
lean_object* v_kFail_1434_ = stack[1].m_obj;
lean_object* v_kSuccess_1435_ = stack[2].m_obj;
lean_object* v___y_1436_ = stack[3].m_obj;
lean_object* v___y_1437_ = stack[4].m_obj;
lean_object* v___y_1438_ = stack[5].m_obj;
lean_object* v___y_1439_ = stack[6].m_obj;
lean_object* v___y_1440_ = stack[7].m_obj;
lean_object* v___y_1441_ = stack[8].m_obj;
lean_object* v___y_1442_ = stack[9].m_obj;
lean_object* v___y_1443_ = stack[10].m_obj;
lean_object* v_res_1525_;
v_res_1525_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_goal_1433_, v_kFail_1434_, v_kSuccess_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___boxed(lean_object* v_goal_1526_, lean_object* v_kFail_1527_, lean_object* v_kSuccess_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_goal_1526_, v_kFail_1527_, v_kSuccess_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(lean_object* v_a_1542_, lean_object* v___f_1543_, lean_object* v___f_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
lean_inc(v_a_1542_);
v___x_1554_ = l_Lean_MVarId_getType(v_a_1542_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_a_1555_, v___y_1550_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1557_);
lean_dec(v_a_1557_);
if (lean_obj_tag(v___x_1558_) == 1)
{
lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_val_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_val_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_val_1559_, v___f_1543_, v___f_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_a_1542_, v_a_1561_, v___y_1550_);
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1542_);
v_a_1563_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1560_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1560_);
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
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v___x_1558_);
lean_dec_ref(v___f_1544_);
lean_dec_ref(v___f_1543_);
lean_dec(v_a_1542_);
v___x_1571_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1);
v___x_1572_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v___x_1571_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1572_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___f_1544_);
lean_dec_ref(v___f_1543_);
lean_dec(v_a_1542_);
v_a_1573_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1554_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1554_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1542_ = stack[0].m_obj;
lean_object* v___f_1543_ = stack[1].m_obj;
lean_object* v___f_1544_ = stack[2].m_obj;
lean_object* v___y_1545_ = stack[3].m_obj;
lean_object* v___y_1546_ = stack[4].m_obj;
lean_object* v___y_1547_ = stack[5].m_obj;
lean_object* v___y_1548_ = stack[6].m_obj;
lean_object* v___y_1549_ = stack[7].m_obj;
lean_object* v___y_1550_ = stack[8].m_obj;
lean_object* v___y_1551_ = stack[9].m_obj;
lean_object* v___y_1552_ = stack[10].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(v_a_1542_, v___f_1543_, v___f_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed(lean_object* v_a_1582_, lean_object* v___f_1583_, lean_object* v___f_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(v_a_1582_, v___f_1583_, v___f_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1594_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___f_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v___f_1606_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0));
v___f_1607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1));
v___x_1608_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1598_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_n(v_a_1609_, 2);
lean_dec_ref_known(v___x_1608_, 1);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1610_, 0, v_a_1609_);
lean_closure_set(v___f_1610_, 1, v___f_1606_);
lean_closure_set(v___f_1610_, 2, v___f_1607_);
v___x_1611_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_a_1609_, v___f_1610_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1611_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1608_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1597_ = stack[0].m_obj;
lean_object* v_a_1598_ = stack[1].m_obj;
lean_object* v_a_1599_ = stack[2].m_obj;
lean_object* v_a_1600_ = stack[3].m_obj;
lean_object* v_a_1601_ = stack[4].m_obj;
lean_object* v_a_1602_ = stack[5].m_obj;
lean_object* v_a_1603_ = stack[6].m_obj;
lean_object* v_a_1604_ = stack[7].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___boxed(lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1630_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(lean_object* v_x_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1631_ = stack[0].m_obj;
lean_object* v_a_1632_ = stack[1].m_obj;
lean_object* v_a_1633_ = stack[2].m_obj;
lean_object* v_a_1634_ = stack[3].m_obj;
lean_object* v_a_1635_ = stack[4].m_obj;
lean_object* v_a_1636_ = stack[5].m_obj;
lean_object* v_a_1637_ = stack[6].m_obj;
lean_object* v_a_1638_ = stack[7].m_obj;
lean_object* v_a_1639_ = stack[8].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(v_x_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed(lean_object* v_x_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(v_x_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_x_1643_);
return v_res_1653_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(lean_object* v_00_u03b1_1654_, lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_1655_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1655_ = stack[1].m_obj;
lean_object* v___y_1656_ = stack[2].m_obj;
lean_object* v___y_1657_ = stack[3].m_obj;
lean_object* v___y_1658_ = stack[4].m_obj;
lean_object* v___y_1659_ = stack[5].m_obj;
lean_object* v___y_1660_ = stack[6].m_obj;
lean_object* v___y_1661_ = stack[7].m_obj;
lean_object* v___y_1662_ = stack[8].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(lean_box(0), v_msg_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(v_00_u03b1_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
return v_res_1676_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(lean_object* v_mvarId_1677_, lean_object* v_val_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1677_, v_val_1678_, v___y_1684_);
return v___x_1688_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1677_ = stack[0].m_obj;
lean_object* v_val_1678_ = stack[1].m_obj;
lean_object* v___y_1679_ = stack[2].m_obj;
lean_object* v___y_1680_ = stack[3].m_obj;
lean_object* v___y_1681_ = stack[4].m_obj;
lean_object* v___y_1682_ = stack[5].m_obj;
lean_object* v___y_1683_ = stack[6].m_obj;
lean_object* v___y_1684_ = stack[7].m_obj;
lean_object* v___y_1685_ = stack[8].m_obj;
lean_object* v___y_1686_ = stack[9].m_obj;
lean_object* v_res_1689_;
v_res_1689_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(v_mvarId_1677_, v_val_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
stack->m_obj
 = v_res_1689_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___boxed(lean_object* v_mvarId_1690_, lean_object* v_val_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(v_mvarId_1690_, v_val_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1701_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(lean_object* v_00_u03b1_1702_, lean_object* v_msg_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1703_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1703_ = stack[1].m_obj;
lean_object* v___y_1704_ = stack[2].m_obj;
lean_object* v___y_1705_ = stack[3].m_obj;
lean_object* v___y_1706_ = stack[4].m_obj;
lean_object* v___y_1707_ = stack[5].m_obj;
lean_object* v___y_1708_ = stack[6].m_obj;
lean_object* v___y_1709_ = stack[7].m_obj;
lean_object* v___y_1710_ = stack[8].m_obj;
lean_object* v___y_1711_ = stack[9].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(lean_box(0), v_msg_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(v_00_u03b1_1715_, v_msg_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1726_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1727_, lean_object* v_name_1728_, uint8_t v_bi_1729_, lean_object* v_type_1730_, lean_object* v_k_1731_, uint8_t v_kind_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1728_, v_bi_1729_, v_type_1730_, v_k_1731_, v_kind_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1728_ = stack[1].m_obj;
uint8_t v_bi_1729_ = stack[2].m_num;
lean_object* v_type_1730_ = stack[3].m_obj;
lean_object* v_k_1731_ = stack[4].m_obj;
uint8_t v_kind_1732_ = stack[5].m_num;
lean_object* v___y_1733_ = stack[6].m_obj;
lean_object* v___y_1734_ = stack[7].m_obj;
lean_object* v___y_1735_ = stack[8].m_obj;
lean_object* v___y_1736_ = stack[9].m_obj;
lean_object* v___y_1737_ = stack[10].m_obj;
lean_object* v___y_1738_ = stack[11].m_obj;
lean_object* v___y_1739_ = stack[12].m_obj;
lean_object* v___y_1740_ = stack[13].m_obj;
lean_object* v_res_1743_;
v_res_1743_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(lean_box(0), v_name_1728_, v_bi_1729_, v_type_1730_, v_k_1731_, v_kind_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
stack->m_obj
 = v_res_1743_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_name_1745_, lean_object* v_bi_1746_, lean_object* v_type_1747_, lean_object* v_k_1748_, lean_object* v_kind_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_bi_boxed_1759_; uint8_t v_kind_boxed_1760_; lean_object* v_res_1761_; 
v_bi_boxed_1759_ = lean_unbox(v_bi_1746_);
v_kind_boxed_1760_ = lean_unbox(v_kind_1749_);
v_res_1761_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(v_00_u03b1_1744_, v_name_1745_, v_bi_boxed_1759_, v_type_1747_, v_k_1748_, v_kind_boxed_1760_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
return v_res_1761_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(lean_object* v_00_u03b1_1762_, lean_object* v_name_1763_, lean_object* v_type_1764_, lean_object* v_k_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1763_, v_type_1764_, v_k_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1763_ = stack[1].m_obj;
lean_object* v_type_1764_ = stack[2].m_obj;
lean_object* v_k_1765_ = stack[3].m_obj;
lean_object* v___y_1766_ = stack[4].m_obj;
lean_object* v___y_1767_ = stack[5].m_obj;
lean_object* v___y_1768_ = stack[6].m_obj;
lean_object* v___y_1769_ = stack[7].m_obj;
lean_object* v___y_1770_ = stack[8].m_obj;
lean_object* v___y_1771_ = stack[9].m_obj;
lean_object* v___y_1772_ = stack[10].m_obj;
lean_object* v___y_1773_ = stack[11].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(lean_box(0), v_name_1763_, v_type_1764_, v_k_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1777_, lean_object* v_name_1778_, lean_object* v_type_1779_, lean_object* v_k_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(v_00_u03b1_1777_, v_name_1778_, v_type_1779_, v_k_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5(lean_object* v_00_u03b2_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_x_1792_, v_x_1793_, v_x_1794_);
return v___x_1795_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1796_, lean_object* v_x_1797_, size_t v_x_1798_, size_t v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1797_, v_x_1798_, v_x_1799_, v_x_1800_, v_x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1797_ = stack[1].m_obj;
size_t v_x_1798_ = stack[2].m_num;
size_t v_x_1799_ = stack[3].m_num;
lean_object* v_x_1800_ = stack[4].m_obj;
lean_object* v_x_1801_ = stack[5].m_obj;
lean_object* v_res_1803_;
v_res_1803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(lean_box(0), v_x_1797_, v_x_1798_, v_x_1799_, v_x_1800_, v_x_1801_);
stack->m_obj
 = v_res_1803_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
size_t v_x_12699__boxed_1810_; size_t v_x_12700__boxed_1811_; lean_object* v_res_1812_; 
v_x_12699__boxed_1810_ = lean_unbox_usize(v_x_1806_);
lean_dec(v_x_1806_);
v_x_12700__boxed_1811_ = lean_unbox_usize(v_x_1807_);
lean_dec(v_x_1807_);
v_res_1812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(v_00_u03b2_1804_, v_x_1805_, v_x_12699__boxed_1810_, v_x_12700__boxed_1811_, v_x_1808_, v_x_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1813_, lean_object* v_n_1814_, lean_object* v_k_1815_, lean_object* v_v_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v_n_1814_, v_k_1815_, v_v_1816_);
return v___x_1817_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1818_, size_t v_depth_1819_, lean_object* v_keys_1820_, lean_object* v_vals_1821_, lean_object* v_heq_1822_, lean_object* v_i_1823_, lean_object* v_entries_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_1819_, v_keys_1820_, v_vals_1821_, v_i_1823_, v_entries_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1819_ = stack[1].m_num;
lean_object* v_keys_1820_ = stack[2].m_obj;
lean_object* v_vals_1821_ = stack[3].m_obj;
lean_object* v_i_1823_ = stack[5].m_obj;
lean_object* v_entries_1824_ = stack[6].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(lean_box(0), v_depth_1819_, v_keys_1820_, v_vals_1821_, lean_box(0), v_i_1823_, v_entries_1824_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1827_, lean_object* v_depth_1828_, lean_object* v_keys_1829_, lean_object* v_vals_1830_, lean_object* v_heq_1831_, lean_object* v_i_1832_, lean_object* v_entries_1833_){
_start:
{
size_t v_depth_boxed_1834_; lean_object* v_res_1835_; 
v_depth_boxed_1834_ = lean_unbox_usize(v_depth_1828_);
lean_dec(v_depth_1828_);
v_res_1835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_1827_, v_depth_boxed_1834_, v_keys_1829_, v_vals_1830_, v_heq_1831_, v_i_1832_, v_entries_1833_);
lean_dec_ref(v_vals_1830_);
lean_dec_ref(v_keys_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_00_u03b2_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_x_1837_, v_x_1838_, v_x_1839_, v_x_1840_);
return v___x_1841_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1(){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3));
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7));
v___x_1864_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed), 10, 0);
v___x_1865_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1861_, v___x_1862_, v___x_1863_, v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1866_;
v_res_1866_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___boxed(lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
return v_res_1868_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
}
#ifdef __cplusplus
}
#endif
