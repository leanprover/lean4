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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(lean_object* v___y_14_){
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg___boxed(lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_50_);
lean_dec(v___y_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___boxed(lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___f_72_; lean_object* v___x_3046__overap_73_; lean_object* v___x_74_; 
v___f_72_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0));
v___x_3046__overap_73_ = lean_panic_fn_borrowed(v___f_72_, v_msg_66_);
lean_inc(v___y_70_);
lean_inc_ref(v___y_69_);
lean_inc(v___y_68_);
lean_inc_ref(v___y_67_);
v___x_74_ = lean_apply_5(v___x_3046__overap_73_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___boxed(lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v_msg_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(lean_object* v_a_85_, lean_object* v_Ps_86_, lean_object* v_a_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_snd_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_179_; 
v_snd_93_ = lean_ctor_get(v_a_87_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_a_87_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_a_87_, 0);
lean_dec(v_unused_180_);
v___x_95_ = v_a_87_;
v_isShared_96_ = v_isSharedCheck_179_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_snd_93_);
lean_dec(v_a_87_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_179_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_box(0);
v___x_98_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_99_ = l_Lean_Core_mkFreshUserName(v___x_98_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_91_);
if (lean_obj_tag(v___x_101_) == 0)
{
if (lean_obj_tag(v_snd_93_) == 1)
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref_known(v___x_101_, 1);
lean_dec(v_a_100_);
v_head_102_ = lean_ctor_get(v_snd_93_, 0);
v_tail_103_ = lean_ctor_get(v_snd_93_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_snd_93_);
if (v_isSharedCheck_147_ == 0)
{
v___x_105_ = v_snd_93_;
v_isShared_106_ = v_isSharedCheck_147_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_tail_103_);
lean_inc(v_head_102_);
lean_dec(v_snd_93_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_147_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_name_107_; lean_object* v_uniq_108_; lean_object* v_p_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_146_; 
v_name_107_ = lean_ctor_get(v_head_102_, 0);
v_uniq_108_ = lean_ctor_get(v_head_102_, 1);
v_p_109_ = lean_ctor_get(v_head_102_, 2);
v_isSharedCheck_146_ = !lean_is_exclusive(v_head_102_);
if (v_isSharedCheck_146_ == 0)
{
v___x_111_ = v_head_102_;
v_isShared_112_ = v_isSharedCheck_146_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_p_109_);
lean_inc(v_uniq_108_);
lean_inc(v_name_107_);
lean_dec(v_head_102_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_146_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; 
lean_inc_ref(v_a_85_);
v___x_113_ = l_Lean_Meta_isExprDefEq(v_p_109_, v_a_85_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_137_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_137_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_137_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_137_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___x_118_; 
v___x_118_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
if (v___x_118_ == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_116_);
lean_del_object(v___x_111_);
lean_dec(v_uniq_108_);
lean_dec(v_name_107_);
lean_del_object(v___x_105_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v_tail_103_);
lean_ctor_set(v___x_95_, 0, v___x_97_);
v___x_120_ = v___x_95_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_tail_103_);
v___x_120_ = v_reuseFailAlloc_122_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
v_a_87_ = v___x_120_;
goto _start;
}
}
else
{
lean_object* v___x_124_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 2, v_a_85_);
v___x_124_ = v___x_111_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_name_107_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_uniq_108_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_a_85_);
v___x_124_ = v_reuseFailAlloc_136_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_124_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___x_125_);
lean_ctor_set(v___x_95_, 0, v_Ps_86_);
v___x_127_ = v___x_95_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_Ps_86_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_135_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 0);
lean_ctor_set(v___x_105_, 0, v___x_128_);
v___x_130_ = v___x_105_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_tail_103_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_130_);
v___x_132_ = v___x_116_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_del_object(v___x_111_);
lean_dec(v_uniq_108_);
lean_dec(v_name_107_);
lean_del_object(v___x_105_);
lean_dec(v_tail_103_);
lean_del_object(v___x_95_);
lean_dec(v_Ps_86_);
lean_dec_ref(v_a_85_);
v_a_138_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_113_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_113_);
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
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_162_; 
v_a_148_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_162_ == 0)
{
v___x_150_ = v___x_101_;
v_isShared_151_ = v_isSharedCheck_162_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_101_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_162_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v_a_100_);
lean_ctor_set(v___x_152_, 1, v_a_148_);
lean_ctor_set(v___x_152_, 2, v_a_85_);
v___x_153_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_152_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___x_153_);
lean_ctor_set(v___x_95_, 0, v_Ps_86_);
v___x_155_ = v___x_95_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_Ps_86_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_153_);
v___x_155_ = v_reuseFailAlloc_161_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_snd_93_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_157_);
v___x_159_ = v___x_150_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_a_100_);
lean_del_object(v___x_95_);
lean_dec(v_snd_93_);
lean_dec(v_Ps_86_);
lean_dec_ref(v_a_85_);
v_a_163_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_101_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_101_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_del_object(v___x_95_);
lean_dec(v_snd_93_);
lean_dec(v_Ps_86_);
lean_dec_ref(v_a_85_);
v_a_171_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_99_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_99_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___boxed(lean_object* v_a_181_, lean_object* v_Ps_182_, lean_object* v_a_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_181_, v_Ps_182_, v_a_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2));
v___x_194_ = lean_unsigned_to_nat(8u);
v___x_195_ = lean_unsigned_to_nat(51u);
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1));
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0));
v___x_198_ = l_mkPanicMessageWithDecl(v___x_197_, v___x_196_, v___x_195_, v___x_194_, v___x_193_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(lean_object* v_Ps_199_, lean_object* v_P_x27_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_P_x27_200_, v_a_202_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_270_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_270_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_270_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_270_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; 
lean_inc(v_a_207_);
v___x_211_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_207_);
if (lean_obj_tag(v___x_211_) == 1)
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec_ref_known(v___x_211_, 1);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_Ps_199_);
lean_ctor_set(v___x_212_, 1, v_a_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v___x_211_);
lean_del_object(v___x_209_);
v___x_216_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_207_);
if (lean_obj_tag(v___x_216_) == 1)
{
lean_object* v_val_217_; lean_object* v_snd_218_; lean_object* v_snd_219_; lean_object* v_fst_220_; lean_object* v_fst_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; 
lean_dec(v_a_207_);
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_216_, 1);
v_snd_218_ = lean_ctor_get(v_val_217_, 1);
lean_inc(v_snd_218_);
v_snd_219_ = lean_ctor_get(v_snd_218_, 1);
lean_inc(v_snd_219_);
v_fst_220_ = lean_ctor_get(v_val_217_, 0);
lean_inc(v_fst_220_);
lean_dec(v_val_217_);
v_fst_221_ = lean_ctor_get(v_snd_218_, 0);
lean_inc(v_fst_221_);
lean_dec(v_snd_218_);
v_fst_222_ = lean_ctor_get(v_snd_219_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_snd_219_, 1);
lean_inc(v_snd_223_);
lean_dec(v_snd_219_);
v___x_224_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_199_, v_fst_222_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v_fst_226_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_a_225_, 1);
lean_inc(v_snd_227_);
lean_dec(v_a_225_);
v___x_228_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_fst_226_, v_snd_223_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_246_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_246_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_246_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_246_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_245_; 
v_fst_233_ = lean_ctor_get(v_a_229_, 0);
v_snd_234_ = lean_ctor_get(v_a_229_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_229_);
if (v_isSharedCheck_245_ == 0)
{
v___x_236_ = v_a_229_;
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_snd_234_);
lean_inc(v_fst_233_);
lean_dec(v_a_229_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_220_, v_fst_221_, v_snd_227_, v_snd_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_240_);
v___x_242_ = v___x_231_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
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
else
{
lean_dec(v_snd_227_);
lean_dec(v_fst_221_);
lean_dec(v_fst_220_);
return v___x_228_;
}
}
else
{
lean_dec(v_snd_223_);
lean_dec(v_fst_221_);
lean_dec(v_fst_220_);
return v___x_224_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v___x_216_);
v___x_247_ = lean_box(0);
lean_inc(v_Ps_199_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_Ps_199_);
v___x_249_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_207_, v_Ps_199_, v___x_248_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_261_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_261_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_261_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_261_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_fst_254_; 
v_fst_254_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_fst_254_);
lean_dec(v_a_250_);
if (lean_obj_tag(v_fst_254_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_del_object(v___x_252_);
v___x_255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3);
v___x_256_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v___x_255_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
return v___x_256_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_259_; 
v_val_257_ = lean_ctor_get(v_fst_254_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v_fst_254_, 1);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_val_257_);
v___x_259_ = v___x_252_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_val_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_249_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_249_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_Ps_199_);
v_a_271_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_206_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_206_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___boxed(lean_object* v_Ps_279_, lean_object* v_P_x27_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_279_, v_P_x27_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(lean_object* v_a_287_, lean_object* v_Ps_288_, lean_object* v_inst_289_, lean_object* v_a_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_287_, v_Ps_288_, v_a_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___boxed(lean_object* v_a_297_, lean_object* v_Ps_298_, lean_object* v_inst_299_, lean_object* v_a_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(v_a_297_, v_Ps_298_, v_inst_299_, v_a_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(lean_object* v_P_307_, lean_object* v_P_x27_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_box(0);
v___x_315_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_P_307_, v___x_314_);
v___x_316_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v___x_315_, v_P_x27_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_snd_321_; lean_object* v___x_323_; 
v_snd_321_ = lean_ctor_get(v_a_317_, 1);
lean_inc(v_snd_321_);
lean_dec(v_a_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_snd_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_snd_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_316_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_316_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed(lean_object* v_P_334_, lean_object* v_P_x27_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_P_334_, v_P_x27_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0(lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_00_u03c3s_349_, lean_object* v_hyps_350_, lean_object* v_P_x27_351_, lean_object* v_target_352_, lean_object* v_00_u03c6_353_, lean_object* v_a_354_, lean_object* v_toPure_355_, lean_object* v_prf_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_prf_361_; lean_object* v___x_362_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_359_ = l_Lean_Name_mkStr6(v___x_344_, v___x_345_, v___x_346_, v___x_347_, v___x_357_, v___x_358_);
v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_348_);
v_prf_361_ = l_Lean_mkApp7(v___x_360_, v_00_u03c3s_349_, v_hyps_350_, v_P_x27_351_, v_target_352_, v_00_u03c6_353_, v_a_354_, v_prf_356_);
v___x_362_ = lean_apply_2(v_toPure_355_, lean_box(0), v_prf_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(lean_object* v_h_u03c6_363_, uint8_t v_____do__lift_364_, uint8_t v___x_365_, lean_object* v_inst_366_, lean_object* v_toBind_367_, lean_object* v___f_368_, lean_object* v_prf_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_mk_empty_array_with_capacity(v___x_370_);
v___x_372_ = lean_array_push(v___x_371_, v_h_u03c6_363_);
v___x_373_ = 1;
v___x_374_ = lean_box(v_____do__lift_364_);
v___x_375_ = lean_box(v___x_365_);
v___x_376_ = lean_box(v_____do__lift_364_);
v___x_377_ = lean_box(v___x_365_);
v___x_378_ = lean_box(v___x_373_);
v___x_379_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_379_, 0, v___x_372_);
lean_closure_set(v___x_379_, 1, v_prf_369_);
lean_closure_set(v___x_379_, 2, v___x_374_);
lean_closure_set(v___x_379_, 3, v___x_375_);
lean_closure_set(v___x_379_, 4, v___x_376_);
lean_closure_set(v___x_379_, 5, v___x_377_);
lean_closure_set(v___x_379_, 6, v___x_378_);
v___x_380_ = lean_apply_2(v_inst_366_, lean_box(0), v___x_379_);
v___x_381_ = lean_apply_4(v_toBind_367_, lean_box(0), lean_box(0), v___x_380_, v___f_368_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed(lean_object* v_h_u03c6_382_, lean_object* v_____do__lift_383_, lean_object* v___x_384_, lean_object* v_inst_385_, lean_object* v_toBind_386_, lean_object* v___f_387_, lean_object* v_prf_388_){
_start:
{
uint8_t v_____do__lift_392__boxed_389_; uint8_t v___x_393__boxed_390_; lean_object* v_res_391_; 
v_____do__lift_392__boxed_389_ = lean_unbox(v_____do__lift_383_);
v___x_393__boxed_390_ = lean_unbox(v___x_384_);
v_res_391_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(v_h_u03c6_382_, v_____do__lift_392__boxed_389_, v___x_393__boxed_390_, v_inst_385_, v_toBind_386_, v___f_387_, v_prf_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(uint8_t v_____do__lift_392_, uint8_t v___x_393_, lean_object* v_inst_394_, lean_object* v_toBind_395_, lean_object* v___f_396_, lean_object* v_kSuccess_397_, lean_object* v_00_u03c6_398_, lean_object* v_goal_399_, lean_object* v_h_u03c6_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_401_ = lean_box(v_____do__lift_392_);
v___x_402_ = lean_box(v___x_393_);
lean_inc(v_toBind_395_);
lean_inc_ref(v_h_u03c6_400_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_403_, 0, v_h_u03c6_400_);
lean_closure_set(v___f_403_, 1, v___x_401_);
lean_closure_set(v___f_403_, 2, v___x_402_);
lean_closure_set(v___f_403_, 3, v_inst_394_);
lean_closure_set(v___f_403_, 4, v_toBind_395_);
lean_closure_set(v___f_403_, 5, v___f_396_);
v___x_404_ = lean_apply_3(v_kSuccess_397_, v_00_u03c6_398_, v_h_u03c6_400_, v_goal_399_);
v___x_405_ = lean_apply_4(v_toBind_395_, lean_box(0), lean_box(0), v___x_404_, v___f_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed(lean_object* v_____do__lift_406_, lean_object* v___x_407_, lean_object* v_inst_408_, lean_object* v_toBind_409_, lean_object* v___f_410_, lean_object* v_kSuccess_411_, lean_object* v_00_u03c6_412_, lean_object* v_goal_413_, lean_object* v_h_u03c6_414_){
_start:
{
uint8_t v_____do__lift_428__boxed_415_; uint8_t v___x_429__boxed_416_; lean_object* v_res_417_; 
v_____do__lift_428__boxed_415_ = lean_unbox(v_____do__lift_406_);
v___x_429__boxed_416_ = lean_unbox(v___x_407_);
v_res_417_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(v_____do__lift_428__boxed_415_, v___x_429__boxed_416_, v_inst_408_, v_toBind_409_, v___f_410_, v_kSuccess_411_, v_00_u03c6_412_, v_goal_413_, v_h_u03c6_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_00_u03c6_420_, lean_object* v___f_421_, lean_object* v_____do__lift_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_418_, v_inst_419_, v_____do__lift_422_, v_00_u03c6_420_, v___f_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(lean_object* v___x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Core_mkFreshUserName(v___x_424_, v___y_427_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed(lean_object* v___x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(v___x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v_00_u03c3s_445_, lean_object* v_hyps_446_, lean_object* v_target_447_, lean_object* v_00_u03c6_448_, lean_object* v_a_449_, lean_object* v_toPure_450_, lean_object* v_u_451_, uint8_t v_____do__lift_452_, uint8_t v___x_453_, lean_object* v_inst_454_, lean_object* v_toBind_455_, lean_object* v_kSuccess_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_P_x27_459_){
_start:
{
lean_object* v___f_460_; lean_object* v_goal_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc_ref_n(v_00_u03c6_448_, 2);
lean_inc_ref(v_target_447_);
lean_inc_ref(v_P_x27_459_);
lean_inc_ref(v_00_u03c3s_445_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0), 13, 12);
lean_closure_set(v___f_460_, 0, v___x_440_);
lean_closure_set(v___f_460_, 1, v___x_441_);
lean_closure_set(v___f_460_, 2, v___x_442_);
lean_closure_set(v___f_460_, 3, v___x_443_);
lean_closure_set(v___f_460_, 4, v___x_444_);
lean_closure_set(v___f_460_, 5, v_00_u03c3s_445_);
lean_closure_set(v___f_460_, 6, v_hyps_446_);
lean_closure_set(v___f_460_, 7, v_P_x27_459_);
lean_closure_set(v___f_460_, 8, v_target_447_);
lean_closure_set(v___f_460_, 9, v_00_u03c6_448_);
lean_closure_set(v___f_460_, 10, v_a_449_);
lean_closure_set(v___f_460_, 11, v_toPure_450_);
v_goal_461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_461_, 0, v_u_451_);
lean_ctor_set(v_goal_461_, 1, v_00_u03c3s_445_);
lean_ctor_set(v_goal_461_, 2, v_P_x27_459_);
lean_ctor_set(v_goal_461_, 3, v_target_447_);
v___x_462_ = lean_box(v_____do__lift_452_);
v___x_463_ = lean_box(v___x_453_);
lean_inc(v_toBind_455_);
lean_inc(v_inst_454_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_464_, 0, v___x_462_);
lean_closure_set(v___f_464_, 1, v___x_463_);
lean_closure_set(v___f_464_, 2, v_inst_454_);
lean_closure_set(v___f_464_, 3, v_toBind_455_);
lean_closure_set(v___f_464_, 4, v___f_460_);
lean_closure_set(v___f_464_, 5, v_kSuccess_456_);
lean_closure_set(v___f_464_, 6, v_00_u03c6_448_);
lean_closure_set(v___f_464_, 7, v_goal_461_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_465_, 0, v_inst_457_);
lean_closure_set(v___f_465_, 1, v_inst_458_);
lean_closure_set(v___f_465_, 2, v_00_u03c6_448_);
lean_closure_set(v___f_465_, 3, v___f_464_);
v___f_466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0));
v___x_467_ = lean_apply_2(v_inst_454_, lean_box(0), v___f_466_);
v___x_468_ = lean_apply_4(v_toBind_455_, lean_box(0), lean_box(0), v___x_467_, v___f_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_469_ = _args[0];
lean_object* v___x_470_ = _args[1];
lean_object* v___x_471_ = _args[2];
lean_object* v___x_472_ = _args[3];
lean_object* v___x_473_ = _args[4];
lean_object* v_00_u03c3s_474_ = _args[5];
lean_object* v_hyps_475_ = _args[6];
lean_object* v_target_476_ = _args[7];
lean_object* v_00_u03c6_477_ = _args[8];
lean_object* v_a_478_ = _args[9];
lean_object* v_toPure_479_ = _args[10];
lean_object* v_u_480_ = _args[11];
lean_object* v_____do__lift_481_ = _args[12];
lean_object* v___x_482_ = _args[13];
lean_object* v_inst_483_ = _args[14];
lean_object* v_toBind_484_ = _args[15];
lean_object* v_kSuccess_485_ = _args[16];
lean_object* v_inst_486_ = _args[17];
lean_object* v_inst_487_ = _args[18];
lean_object* v_P_x27_488_ = _args[19];
_start:
{
uint8_t v_____do__lift_493__boxed_489_; uint8_t v___x_494__boxed_490_; lean_object* v_res_491_; 
v_____do__lift_493__boxed_489_ = lean_unbox(v_____do__lift_481_);
v___x_494__boxed_490_ = lean_unbox(v___x_482_);
v_res_491_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(v___x_469_, v___x_470_, v___x_471_, v___x_472_, v___x_473_, v_00_u03c3s_474_, v_hyps_475_, v_target_476_, v_00_u03c6_477_, v_a_478_, v_toPure_479_, v_u_480_, v_____do__lift_493__boxed_489_, v___x_494__boxed_490_, v_inst_483_, v_toBind_484_, v_kSuccess_485_, v_inst_486_, v_inst_487_, v_P_x27_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_00_u03c3s_497_, lean_object* v_hyps_498_, lean_object* v_target_499_, lean_object* v_00_u03c6_500_, lean_object* v_a_501_, lean_object* v_toPure_502_, lean_object* v_u_503_, lean_object* v_inst_504_, lean_object* v_toBind_505_, lean_object* v_kSuccess_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_P_x27_509_, lean_object* v_kFail_510_, uint8_t v_____do__lift_511_){
_start:
{
if (v_____do__lift_511_ == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_512_ = 1;
v___x_513_ = lean_box(v_____do__lift_511_);
v___x_514_ = lean_box(v___x_512_);
lean_inc(v_toBind_505_);
lean_inc(v_inst_504_);
lean_inc_ref(v_hyps_498_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed), 20, 19);
lean_closure_set(v___f_515_, 0, v___x_492_);
lean_closure_set(v___f_515_, 1, v___x_493_);
lean_closure_set(v___f_515_, 2, v___x_494_);
lean_closure_set(v___f_515_, 3, v___x_495_);
lean_closure_set(v___f_515_, 4, v___x_496_);
lean_closure_set(v___f_515_, 5, v_00_u03c3s_497_);
lean_closure_set(v___f_515_, 6, v_hyps_498_);
lean_closure_set(v___f_515_, 7, v_target_499_);
lean_closure_set(v___f_515_, 8, v_00_u03c6_500_);
lean_closure_set(v___f_515_, 9, v_a_501_);
lean_closure_set(v___f_515_, 10, v_toPure_502_);
lean_closure_set(v___f_515_, 11, v_u_503_);
lean_closure_set(v___f_515_, 12, v___x_513_);
lean_closure_set(v___f_515_, 13, v___x_514_);
lean_closure_set(v___f_515_, 14, v_inst_504_);
lean_closure_set(v___f_515_, 15, v_toBind_505_);
lean_closure_set(v___f_515_, 16, v_kSuccess_506_);
lean_closure_set(v___f_515_, 17, v_inst_507_);
lean_closure_set(v___f_515_, 18, v_inst_508_);
v___x_516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed), 7, 2);
lean_closure_set(v___x_516_, 0, v_hyps_498_);
lean_closure_set(v___x_516_, 1, v_P_x27_509_);
v___x_517_ = lean_apply_2(v_inst_504_, lean_box(0), v___x_516_);
v___x_518_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_517_, v___f_515_);
return v___x_518_;
}
else
{
lean_dec_ref(v_P_x27_509_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_kSuccess_506_);
lean_dec(v_toBind_505_);
lean_dec(v_inst_504_);
lean_dec(v_u_503_);
lean_dec(v_toPure_502_);
lean_dec_ref(v_a_501_);
lean_dec_ref(v_00_u03c6_500_);
lean_dec_ref(v_target_499_);
lean_dec_ref(v_hyps_498_);
lean_dec_ref(v_00_u03c3s_497_);
lean_dec(v___x_496_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec_ref(v___x_493_);
lean_dec_ref(v___x_492_);
lean_inc(v_kFail_510_);
return v_kFail_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_519_ = _args[0];
lean_object* v___x_520_ = _args[1];
lean_object* v___x_521_ = _args[2];
lean_object* v___x_522_ = _args[3];
lean_object* v___x_523_ = _args[4];
lean_object* v_00_u03c3s_524_ = _args[5];
lean_object* v_hyps_525_ = _args[6];
lean_object* v_target_526_ = _args[7];
lean_object* v_00_u03c6_527_ = _args[8];
lean_object* v_a_528_ = _args[9];
lean_object* v_toPure_529_ = _args[10];
lean_object* v_u_530_ = _args[11];
lean_object* v_inst_531_ = _args[12];
lean_object* v_toBind_532_ = _args[13];
lean_object* v_kSuccess_533_ = _args[14];
lean_object* v_inst_534_ = _args[15];
lean_object* v_inst_535_ = _args[16];
lean_object* v_P_x27_536_ = _args[17];
lean_object* v_kFail_537_ = _args[18];
lean_object* v_____do__lift_538_ = _args[19];
_start:
{
uint8_t v_____do__lift_547__boxed_539_; lean_object* v_res_540_; 
v_____do__lift_547__boxed_539_ = lean_unbox(v_____do__lift_538_);
v_res_540_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(v___x_519_, v___x_520_, v___x_521_, v___x_522_, v___x_523_, v_00_u03c3s_524_, v_hyps_525_, v_target_526_, v_00_u03c6_527_, v_a_528_, v_toPure_529_, v_u_530_, v_inst_531_, v_toBind_532_, v_kSuccess_533_, v_inst_534_, v_inst_535_, v_P_x27_536_, v_kFail_537_, v_____do__lift_547__boxed_539_);
lean_dec(v_kFail_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v_00_u03c3s_549_, lean_object* v_hyps_550_, lean_object* v_target_551_, lean_object* v_00_u03c6_552_, lean_object* v_toPure_553_, lean_object* v_u_554_, lean_object* v_inst_555_, lean_object* v_toBind_556_, lean_object* v_kSuccess_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_P_x27_560_, lean_object* v_kFail_561_, lean_object* v___x_562_, lean_object* v_____do__lift_563_){
_start:
{
if (lean_obj_tag(v_____do__lift_563_) == 1)
{
lean_object* v_a_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_a_564_ = lean_ctor_get(v_____do__lift_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v_____do__lift_563_, 1);
lean_inc(v_toBind_556_);
lean_inc(v_inst_555_);
lean_inc_ref(v_00_u03c6_552_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed), 20, 19);
lean_closure_set(v___f_565_, 0, v___x_544_);
lean_closure_set(v___f_565_, 1, v___x_545_);
lean_closure_set(v___f_565_, 2, v___x_546_);
lean_closure_set(v___f_565_, 3, v___x_547_);
lean_closure_set(v___f_565_, 4, v___x_548_);
lean_closure_set(v___f_565_, 5, v_00_u03c3s_549_);
lean_closure_set(v___f_565_, 6, v_hyps_550_);
lean_closure_set(v___f_565_, 7, v_target_551_);
lean_closure_set(v___f_565_, 8, v_00_u03c6_552_);
lean_closure_set(v___f_565_, 9, v_a_564_);
lean_closure_set(v___f_565_, 10, v_toPure_553_);
lean_closure_set(v___f_565_, 11, v_u_554_);
lean_closure_set(v___f_565_, 12, v_inst_555_);
lean_closure_set(v___f_565_, 13, v_toBind_556_);
lean_closure_set(v___f_565_, 14, v_kSuccess_557_);
lean_closure_set(v___f_565_, 15, v_inst_558_);
lean_closure_set(v___f_565_, 16, v_inst_559_);
lean_closure_set(v___f_565_, 17, v_P_x27_560_);
lean_closure_set(v___f_565_, 18, v_kFail_561_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1));
v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_562_);
v___x_568_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_568_, 0, v___x_567_);
lean_closure_set(v___x_568_, 1, v_00_u03c6_552_);
v___x_569_ = lean_apply_2(v_inst_555_, lean_box(0), v___x_568_);
v___x_570_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_569_, v___f_565_);
return v___x_570_;
}
else
{
lean_dec(v_____do__lift_563_);
lean_dec(v___x_562_);
lean_dec_ref(v_P_x27_560_);
lean_dec_ref(v_inst_559_);
lean_dec_ref(v_inst_558_);
lean_dec(v_kSuccess_557_);
lean_dec(v_toBind_556_);
lean_dec(v_inst_555_);
lean_dec(v_u_554_);
lean_dec(v_toPure_553_);
lean_dec_ref(v_00_u03c6_552_);
lean_dec_ref(v_target_551_);
lean_dec_ref(v_hyps_550_);
lean_dec_ref(v_00_u03c3s_549_);
lean_dec(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_545_);
lean_dec_ref(v___x_544_);
return v_kFail_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v___x_571_ = _args[0];
lean_object* v___x_572_ = _args[1];
lean_object* v___x_573_ = _args[2];
lean_object* v___x_574_ = _args[3];
lean_object* v___x_575_ = _args[4];
lean_object* v_00_u03c3s_576_ = _args[5];
lean_object* v_hyps_577_ = _args[6];
lean_object* v_target_578_ = _args[7];
lean_object* v_00_u03c6_579_ = _args[8];
lean_object* v_toPure_580_ = _args[9];
lean_object* v_u_581_ = _args[10];
lean_object* v_inst_582_ = _args[11];
lean_object* v_toBind_583_ = _args[12];
lean_object* v_kSuccess_584_ = _args[13];
lean_object* v_inst_585_ = _args[14];
lean_object* v_inst_586_ = _args[15];
lean_object* v_P_x27_587_ = _args[16];
lean_object* v_kFail_588_ = _args[17];
lean_object* v___x_589_ = _args[18];
lean_object* v_____do__lift_590_ = _args[19];
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(v___x_571_, v___x_572_, v___x_573_, v___x_574_, v___x_575_, v_00_u03c3s_576_, v_hyps_577_, v_target_578_, v_00_u03c6_579_, v_toPure_580_, v_u_581_, v_inst_582_, v_toBind_583_, v_kSuccess_584_, v_inst_585_, v_inst_586_, v_P_x27_587_, v_kFail_588_, v___x_589_, v_____do__lift_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_00_u03c3s_598_, lean_object* v_hyps_599_, lean_object* v_target_600_, lean_object* v_00_u03c6_601_, lean_object* v_toPure_602_, lean_object* v_u_603_, lean_object* v_inst_604_, lean_object* v_toBind_605_, lean_object* v_kSuccess_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_kFail_609_, lean_object* v___x_610_, lean_object* v_P_x27_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
lean_inc_ref(v_P_x27_611_);
lean_inc(v_toBind_605_);
lean_inc(v_inst_604_);
lean_inc_ref(v_00_u03c6_601_);
lean_inc_ref(v_hyps_599_);
lean_inc_ref(v_00_u03c3s_598_);
lean_inc(v___x_597_);
lean_inc_ref(v___x_596_);
lean_inc_ref(v___x_595_);
lean_inc_ref(v___x_594_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed), 20, 19);
lean_closure_set(v___f_613_, 0, v___x_594_);
lean_closure_set(v___f_613_, 1, v___x_595_);
lean_closure_set(v___f_613_, 2, v___x_596_);
lean_closure_set(v___f_613_, 3, v___x_612_);
lean_closure_set(v___f_613_, 4, v___x_597_);
lean_closure_set(v___f_613_, 5, v_00_u03c3s_598_);
lean_closure_set(v___f_613_, 6, v_hyps_599_);
lean_closure_set(v___f_613_, 7, v_target_600_);
lean_closure_set(v___f_613_, 8, v_00_u03c6_601_);
lean_closure_set(v___f_613_, 9, v_toPure_602_);
lean_closure_set(v___f_613_, 10, v_u_603_);
lean_closure_set(v___f_613_, 11, v_inst_604_);
lean_closure_set(v___f_613_, 12, v_toBind_605_);
lean_closure_set(v___f_613_, 13, v_kSuccess_606_);
lean_closure_set(v___f_613_, 14, v_inst_607_);
lean_closure_set(v___f_613_, 15, v_inst_608_);
lean_closure_set(v___f_613_, 16, v_P_x27_611_);
lean_closure_set(v___f_613_, 17, v_kFail_609_);
lean_closure_set(v___f_613_, 18, v___x_610_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1));
v___x_615_ = l_Lean_Name_mkStr5(v___x_594_, v___x_595_, v___x_596_, v___x_612_, v___x_614_);
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_597_);
v___x_617_ = l_Lean_mkApp4(v___x_616_, v_00_u03c3s_598_, v_hyps_599_, v_P_x27_611_, v_00_u03c6_601_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_closure((void*)(l_Lean_Meta_trySynthInstance___boxed), 7, 2);
lean_closure_set(v___x_619_, 0, v___x_617_);
lean_closure_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_apply_2(v_inst_604_, lean_box(0), v___x_619_);
v___x_621_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_620_, v___f_613_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed(lean_object** _args){
lean_object* v___x_622_ = _args[0];
lean_object* v___x_623_ = _args[1];
lean_object* v___x_624_ = _args[2];
lean_object* v___x_625_ = _args[3];
lean_object* v_00_u03c3s_626_ = _args[4];
lean_object* v_hyps_627_ = _args[5];
lean_object* v_target_628_ = _args[6];
lean_object* v_00_u03c6_629_ = _args[7];
lean_object* v_toPure_630_ = _args[8];
lean_object* v_u_631_ = _args[9];
lean_object* v_inst_632_ = _args[10];
lean_object* v_toBind_633_ = _args[11];
lean_object* v_kSuccess_634_ = _args[12];
lean_object* v_inst_635_ = _args[13];
lean_object* v_inst_636_ = _args[14];
lean_object* v_kFail_637_ = _args[15];
lean_object* v___x_638_ = _args[16];
lean_object* v_P_x27_639_ = _args[17];
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(v___x_622_, v___x_623_, v___x_624_, v___x_625_, v_00_u03c3s_626_, v_hyps_627_, v_target_628_, v_00_u03c6_629_, v_toPure_630_, v_u_631_, v_inst_632_, v_toBind_633_, v_kSuccess_634_, v_inst_635_, v_inst_636_, v_kFail_637_, v___x_638_, v_P_x27_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(lean_object* v_u_648_, lean_object* v_00_u03c3s_649_, lean_object* v_hyps_650_, lean_object* v_target_651_, lean_object* v_toPure_652_, lean_object* v_inst_653_, lean_object* v_toBind_654_, lean_object* v_kSuccess_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_kFail_658_, uint8_t v___x_659_, lean_object* v___x_660_, lean_object* v_00_u03c6_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_662_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0));
v___x_663_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1));
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2));
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3));
v___x_666_ = lean_box(0);
lean_inc(v_u_648_);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v_u_648_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v_toBind_654_);
lean_inc(v_inst_653_);
lean_inc_ref(v_00_u03c3s_649_);
lean_inc_ref(v___x_667_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed), 18, 17);
lean_closure_set(v___f_668_, 0, v___x_662_);
lean_closure_set(v___f_668_, 1, v___x_663_);
lean_closure_set(v___f_668_, 2, v___x_664_);
lean_closure_set(v___f_668_, 3, v___x_667_);
lean_closure_set(v___f_668_, 4, v_00_u03c3s_649_);
lean_closure_set(v___f_668_, 5, v_hyps_650_);
lean_closure_set(v___f_668_, 6, v_target_651_);
lean_closure_set(v___f_668_, 7, v_00_u03c6_661_);
lean_closure_set(v___f_668_, 8, v_toPure_652_);
lean_closure_set(v___f_668_, 9, v_u_648_);
lean_closure_set(v___f_668_, 10, v_inst_653_);
lean_closure_set(v___f_668_, 11, v_toBind_654_);
lean_closure_set(v___f_668_, 12, v_kSuccess_655_);
lean_closure_set(v___f_668_, 13, v_inst_656_);
lean_closure_set(v___f_668_, 14, v_inst_657_);
lean_closure_set(v___f_668_, 15, v_kFail_658_);
lean_closure_set(v___f_668_, 16, v___x_666_);
v___x_669_ = l_Lean_mkConst(v___x_665_, v___x_667_);
v___x_670_ = l_Lean_Expr_app___override(v___x_669_, v_00_u03c3s_649_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = lean_box(v___x_659_);
v___x_673_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_673_, 0, v___x_671_);
lean_closure_set(v___x_673_, 1, v___x_672_);
lean_closure_set(v___x_673_, 2, v___x_660_);
v___x_674_ = lean_apply_2(v_inst_653_, lean_box(0), v___x_673_);
v___x_675_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_674_, v___f_668_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed(lean_object* v_u_676_, lean_object* v_00_u03c3s_677_, lean_object* v_hyps_678_, lean_object* v_target_679_, lean_object* v_toPure_680_, lean_object* v_inst_681_, lean_object* v_toBind_682_, lean_object* v_kSuccess_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_kFail_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v_00_u03c6_689_){
_start:
{
uint8_t v___x_702__boxed_690_; lean_object* v_res_691_; 
v___x_702__boxed_690_ = lean_unbox(v___x_687_);
v_res_691_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(v_u_676_, v_00_u03c3s_677_, v_hyps_678_, v_target_679_, v_toPure_680_, v_inst_681_, v_toBind_682_, v_kSuccess_683_, v_inst_684_, v_inst_685_, v_kFail_686_, v___x_702__boxed_690_, v___x_688_, v_00_u03c6_689_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_mkSort(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2(void){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_696_ = lean_box(0);
v___x_697_ = 0;
v___x_698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1);
v___x_699_ = lean_box(v___x_697_);
v___x_700_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshExprMVar___boxed), 8, 3);
lean_closure_set(v___x_700_, 0, v___x_698_);
lean_closure_set(v___x_700_, 1, v___x_699_);
lean_closure_set(v___x_700_, 2, v___x_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_goal_704_, lean_object* v_kFail_705_, lean_object* v_kSuccess_706_){
_start:
{
lean_object* v_toApplicative_707_; lean_object* v_u_708_; lean_object* v_00_u03c3s_709_; lean_object* v_hyps_710_; lean_object* v_target_711_; lean_object* v_toBind_712_; lean_object* v_toPure_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___x_720_; 
v_toApplicative_707_ = lean_ctor_get(v_inst_701_, 0);
v_u_708_ = lean_ctor_get(v_goal_704_, 0);
lean_inc(v_u_708_);
v_00_u03c3s_709_ = lean_ctor_get(v_goal_704_, 1);
lean_inc_ref(v_00_u03c3s_709_);
v_hyps_710_ = lean_ctor_get(v_goal_704_, 2);
lean_inc_ref(v_hyps_710_);
v_target_711_ = lean_ctor_get(v_goal_704_, 3);
lean_inc_ref(v_target_711_);
lean_dec_ref(v_goal_704_);
v_toBind_712_ = lean_ctor_get(v_inst_701_, 1);
lean_inc_n(v_toBind_712_, 2);
v_toPure_713_ = lean_ctor_get(v_toApplicative_707_, 1);
lean_inc(v_toPure_713_);
v___x_714_ = 0;
v___x_715_ = lean_box(0);
v___x_716_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2);
lean_inc(v_inst_703_);
v___x_717_ = lean_apply_2(v_inst_703_, lean_box(0), v___x_716_);
v___x_718_ = lean_box(v___x_714_);
v___f_719_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_719_, 0, v_u_708_);
lean_closure_set(v___f_719_, 1, v_00_u03c3s_709_);
lean_closure_set(v___f_719_, 2, v_hyps_710_);
lean_closure_set(v___f_719_, 3, v_target_711_);
lean_closure_set(v___f_719_, 4, v_toPure_713_);
lean_closure_set(v___f_719_, 5, v_inst_703_);
lean_closure_set(v___f_719_, 6, v_toBind_712_);
lean_closure_set(v___f_719_, 7, v_kSuccess_706_);
lean_closure_set(v___f_719_, 8, v_inst_702_);
lean_closure_set(v___f_719_, 9, v_inst_701_);
lean_closure_set(v___f_719_, 10, v_kFail_705_);
lean_closure_set(v___f_719_, 11, v___x_718_);
lean_closure_set(v___f_719_, 12, v___x_715_);
v___x_720_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_717_, v___f_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore(lean_object* v_m_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_goal_725_, lean_object* v_kFail_726_, lean_object* v_kSuccess_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_722_, v_inst_723_, v_inst_724_, v_goal_725_, v_kFail_726_, v_kSuccess_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(lean_object* v_k_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_goal_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_apply_1(v_k_729_, v_goal_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed(lean_object* v_k_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_goal_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(v_k_734_, v_x_735_, v_x_736_, v_goal_737_);
lean_dec_ref(v_x_736_);
lean_dec_ref(v_x_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_goal_742_, lean_object* v_k_743_){
_start:
{
lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc(v_k_743_);
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_744_, 0, v_k_743_);
lean_inc_ref(v_goal_742_);
v___x_745_ = lean_apply_1(v_k_743_, v_goal_742_);
v___x_746_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_739_, v_inst_740_, v_inst_741_, v_goal_742_, v___x_745_, v___f_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame(lean_object* v_m_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_goal_751_, lean_object* v_k_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(v_inst_748_, v_inst_749_, v_inst_750_, v_goal_751_, v_k_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(lean_object* v_e_754_, lean_object* v___y_755_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = l_Lean_Expr_hasMVar(v_e_754_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_e_754_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v_mctx_760_; lean_object* v___x_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_764_; lean_object* v_cache_765_; lean_object* v_zetaDeltaFVarIds_766_; lean_object* v_postponed_767_; lean_object* v_diag_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v___x_759_ = lean_st_ref_get(v___y_755_);
v_mctx_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_mctx_760_);
lean_dec(v___x_759_);
v___x_761_ = l_Lean_instantiateMVarsCore(v_mctx_760_, v_e_754_);
v_fst_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_fst_762_);
v_snd_763_ = lean_ctor_get(v___x_761_, 1);
lean_inc(v_snd_763_);
lean_dec_ref(v___x_761_);
v___x_764_ = lean_st_ref_take(v___y_755_);
v_cache_765_ = lean_ctor_get(v___x_764_, 1);
v_zetaDeltaFVarIds_766_ = lean_ctor_get(v___x_764_, 2);
v_postponed_767_ = lean_ctor_get(v___x_764_, 3);
v_diag_768_ = lean_ctor_get(v___x_764_, 4);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_778_);
v___x_770_ = v___x_764_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_diag_768_);
lean_inc(v_postponed_767_);
lean_inc(v_zetaDeltaFVarIds_766_);
lean_inc(v_cache_765_);
lean_dec(v___x_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_snd_763_);
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_snd_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_cache_765_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_zetaDeltaFVarIds_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_postponed_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_diag_768_);
v___x_773_ = v_reuseFailAlloc_776_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_st_ref_put(v___y_755_, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_fst_762_);
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg___boxed(lean_object* v_e_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_779_, v___y_780_);
lean_dec(v___y_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(lean_object* v_e_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_783_, v___y_789_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___boxed(lean_object* v_e_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(v_e_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
v___x_815_ = lean_apply_9(v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, lean_box(0));
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed(lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(v_x_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(lean_object* v_mvarId_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_839_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_838_, 0, v_x_828_);
lean_closure_set(v___f_838_, 1, v___y_829_);
lean_closure_set(v___f_838_, 2, v___y_830_);
lean_closure_set(v___f_838_, 3, v___y_831_);
lean_closure_set(v___f_838_, 4, v___y_832_);
v___x_839_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_827_, v___f_838_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___boxed(lean_object* v_mvarId_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(lean_object* v_00_u03b1_860_, lean_object* v_mvarId_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_861_, v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___boxed(lean_object* v_00_u03b1_873_, lean_object* v_mvarId_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(v_00_u03b1_873_, v_mvarId_874_, v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(lean_object* v_msgData_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; lean_object* v_toCold_895_; lean_object* v_mctx_896_; lean_object* v_lctx_897_; lean_object* v_options_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_892_ = lean_st_ref_get(v___y_890_);
v_env_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_892_);
v___x_894_ = lean_st_ref_get(v___y_888_);
v_toCold_895_ = lean_ctor_get(v___y_889_, 0);
v_mctx_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_896_);
lean_dec(v___x_894_);
v_lctx_897_ = lean_ctor_get(v___y_887_, 2);
v_options_898_ = lean_ctor_get(v_toCold_895_, 2);
lean_inc_ref(v_options_898_);
lean_inc_ref(v_lctx_897_);
v___x_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_899_, 0, v_env_893_);
lean_ctor_set(v___x_899_, 1, v_mctx_896_);
lean_ctor_set(v___x_899_, 2, v_lctx_897_);
lean_ctor_set(v___x_899_, 3, v_options_898_);
v___x_900_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_msgData_886_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0___boxed(lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msgData_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_ref_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_ref_915_ = lean_ctor_get(v___y_912_, 2);
v___x_916_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc(v_ref_915_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_ref_915_);
lean_ctor_set(v___x_921_, 1, v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
lean_ctor_set(v___x_919_, 0, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg___boxed(lean_object* v_msg_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1);
v___x_946_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v___x_945_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed(lean_object* v_x_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(v_x_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v_x_947_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_goal_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_959_);
v___x_970_ = lean_box(0);
v___x_971_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_969_, v___x_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Expr_mvarId_x21(v_a_972_);
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_975_, v___y_961_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_976_, 0);
lean_dec(v_unused_984_);
v___x_978_ = v___x_976_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_dec(v___x_976_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_a_972_);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_972_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_972_);
v_a_985_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_976_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_976_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_goal_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(v_x_993_, v_x_994_, v_goal_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v_x_994_);
lean_dec_ref(v_x_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v_ks_1010_; lean_object* v_vs_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1035_; 
v_ks_1010_ = lean_ctor_get(v_x_1006_, 0);
v_vs_1011_ = lean_ctor_get(v_x_1006_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1013_ = v_x_1006_;
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_vs_1011_);
lean_inc(v_ks_1010_);
lean_dec(v_x_1006_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_array_get_size(v_ks_1010_);
v___x_1016_ = lean_nat_dec_lt(v_x_1007_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_dec(v_x_1007_);
v___x_1017_ = lean_array_push(v_ks_1010_, v_x_1008_);
v___x_1018_ = lean_array_push(v_vs_1011_, v_x_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1018_);
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1020_ = v___x_1013_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
else
{
lean_object* v_k_x27_1022_; uint8_t v___x_1023_; 
v_k_x27_1022_ = lean_array_fget_borrowed(v_ks_1010_, v_x_1007_);
v___x_1023_ = l_Lean_instBEqMVarId_beq(v_x_1008_, v_k_x27_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1025_; 
if (v_isShared_1014_ == 0)
{
v___x_1025_ = v___x_1013_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_ks_1010_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_vs_1011_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_x_1007_, v___x_1026_);
lean_dec(v_x_1007_);
v_x_1006_ = v___x_1025_;
v_x_1007_ = v___x_1027_;
goto _start;
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_array_fset(v_ks_1010_, v_x_1007_, v_x_1008_);
v___x_1031_ = lean_array_fset(v_vs_1011_, v_x_1007_, v_x_1009_);
lean_dec(v_x_1007_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1031_);
lean_ctor_set(v___x_1013_, 0, v___x_1030_);
v___x_1033_ = v___x_1013_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_n_1036_, lean_object* v_k_1037_, lean_object* v_v_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_n_1036_, v___x_1039_, v_k_1037_, v_v_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(lean_object* v_x_1042_, size_t v_x_1043_, size_t v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v_es_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v_j_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_es_1047_ = lean_ctor_get(v_x_1042_, 0);
v___x_1048_ = ((size_t)31ULL);
v___x_1049_ = lean_usize_land(v_x_1043_, v___x_1048_);
v_j_1050_ = lean_usize_to_nat(v___x_1049_);
v___x_1051_ = lean_array_get_size(v_es_1047_);
v___x_1052_ = lean_nat_dec_lt(v_j_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_dec(v_j_1050_);
lean_dec(v_x_1046_);
lean_dec(v_x_1045_);
return v_x_1042_;
}
else
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1091_; 
lean_inc_ref(v_es_1047_);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_x_1042_, 0);
lean_dec(v_unused_1092_);
v___x_1054_ = v_x_1042_;
v_isShared_1055_ = v_isSharedCheck_1091_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v_x_1042_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1091_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_v_1056_; lean_object* v___x_1057_; lean_object* v_xs_x27_1058_; lean_object* v___y_1060_; 
v_v_1056_ = lean_array_fget(v_es_1047_, v_j_1050_);
v___x_1057_ = lean_box(0);
v_xs_x27_1058_ = lean_array_fset(v_es_1047_, v_j_1050_, v___x_1057_);
switch(lean_obj_tag(v_v_1056_))
{
case 0:
{
lean_object* v_key_1065_; lean_object* v_val_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_key_1065_ = lean_ctor_get(v_v_1056_, 0);
v_val_1066_ = lean_ctor_get(v_v_1056_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_v_1056_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1068_ = v_v_1056_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_val_1066_);
lean_inc(v_key_1065_);
lean_dec(v_v_1056_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; 
v___x_1070_ = l_Lean_instBEqMVarId_beq(v_x_1045_, v_key_1065_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_del_object(v___x_1068_);
v___x_1071_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1065_, v_val_1066_, v_x_1045_, v_x_1046_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___y_1060_ = v___x_1072_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1074_; 
lean_dec(v_val_1066_);
lean_dec(v_key_1065_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v_x_1046_);
lean_ctor_set(v___x_1068_, 0, v_x_1045_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_x_1045_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_x_1046_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
v___y_1060_ = v___x_1074_;
goto v___jp_1059_;
}
}
}
}
case 1:
{
lean_object* v_node_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1089_; 
v_node_1077_ = lean_ctor_get(v_v_1056_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_v_1056_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1079_ = v_v_1056_;
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_node_1077_);
lean_dec(v_v_1056_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1081_ = ((size_t)5ULL);
v___x_1082_ = lean_usize_shift_right(v_x_1043_, v___x_1081_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_x_1044_, v___x_1083_);
v___x_1085_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_node_1077_, v___x_1082_, v___x_1084_, v_x_1045_, v_x_1046_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1085_);
v___x_1087_ = v___x_1079_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v___y_1060_ = v___x_1087_;
goto v___jp_1059_;
}
}
}
default: 
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_x_1045_);
lean_ctor_set(v___x_1090_, 1, v_x_1046_);
v___y_1060_ = v___x_1090_;
goto v___jp_1059_;
}
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_array_fset(v_xs_x27_1058_, v_j_1050_, v___y_1060_);
lean_dec(v_j_1050_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1061_);
v___x_1063_ = v___x_1054_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
else
{
lean_object* v_ks_1093_; lean_object* v_vs_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1112_; 
v_ks_1093_ = lean_ctor_get(v_x_1042_, 0);
v_vs_1094_ = lean_ctor_get(v_x_1042_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1042_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1096_ = v_x_1042_;
v_isShared_1097_ = v_isSharedCheck_1112_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_vs_1094_);
lean_inc(v_ks_1093_);
lean_dec(v_x_1042_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1112_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_ks_1093_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_vs_1094_);
v___x_1099_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v_newNode_1100_; size_t v___x_1101_; uint8_t v___x_1102_; 
v_newNode_1100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v___x_1099_, v_x_1045_, v_x_1046_);
v___x_1101_ = ((size_t)7ULL);
v___x_1102_ = lean_usize_dec_le(v___x_1101_, v_x_1044_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1100_);
v___x_1104_ = lean_unsigned_to_nat(4u);
v___x_1105_ = lean_nat_dec_lt(v___x_1103_, v___x_1104_);
lean_dec(v___x_1103_);
if (v___x_1105_ == 0)
{
lean_object* v_ks_1106_; lean_object* v_vs_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_ks_1106_ = lean_ctor_get(v_newNode_1100_, 0);
lean_inc_ref(v_ks_1106_);
v_vs_1107_ = lean_ctor_get(v_newNode_1100_, 1);
lean_inc_ref(v_vs_1107_);
lean_dec_ref(v_newNode_1100_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_1110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_x_1044_, v_ks_1106_, v_vs_1107_, v___x_1108_, v___x_1109_);
lean_dec_ref(v_vs_1107_);
lean_dec_ref(v_ks_1106_);
return v___x_1110_;
}
else
{
return v_newNode_1100_;
}
}
else
{
return v_newNode_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(size_t v_depth_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_i_1116_, lean_object* v_entries_1117_){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_array_get_size(v_keys_1114_);
v___x_1119_ = lean_nat_dec_lt(v_i_1116_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v_i_1116_);
return v_entries_1117_;
}
else
{
lean_object* v_k_1120_; lean_object* v_v_1121_; uint64_t v___x_1122_; size_t v_h_1123_; size_t v___x_1124_; lean_object* v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; size_t v_h_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_k_1120_ = lean_array_fget_borrowed(v_keys_1114_, v_i_1116_);
v_v_1121_ = lean_array_fget_borrowed(v_vals_1115_, v_i_1116_);
v___x_1122_ = l_Lean_instHashableMVarId_hash(v_k_1120_);
v_h_1123_ = lean_uint64_to_usize(v___x_1122_);
v___x_1124_ = ((size_t)5ULL);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_sub(v_depth_1113_, v___x_1126_);
v___x_1128_ = lean_usize_mul(v___x_1124_, v___x_1127_);
v_h_1129_ = lean_usize_shift_right(v_h_1123_, v___x_1128_);
v___x_1130_ = lean_nat_add(v_i_1116_, v___x_1125_);
lean_dec(v_i_1116_);
lean_inc(v_v_1121_);
lean_inc(v_k_1120_);
v___x_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_entries_1117_, v_h_1129_, v_depth_1113_, v_k_1120_, v_v_1121_);
v_i_1116_ = v___x_1130_;
v_entries_1117_ = v___x_1131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_depth_1133_, lean_object* v_keys_1134_, lean_object* v_vals_1135_, lean_object* v_i_1136_, lean_object* v_entries_1137_){
_start:
{
size_t v_depth_boxed_1138_; lean_object* v_res_1139_; 
v_depth_boxed_1138_ = lean_unbox_usize(v_depth_1133_);
lean_dec(v_depth_1133_);
v_res_1139_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_boxed_1138_, v_keys_1134_, v_vals_1135_, v_i_1136_, v_entries_1137_);
lean_dec_ref(v_vals_1135_);
lean_dec_ref(v_keys_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_10955__boxed_1145_; size_t v_x_10956__boxed_1146_; lean_object* v_res_1147_; 
v_x_10955__boxed_1145_ = lean_unbox_usize(v_x_1141_);
lean_dec(v_x_1141_);
v_x_10956__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1140_, v_x_10955__boxed_1145_, v_x_10956__boxed_1146_, v_x_1143_, v_x_1144_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
uint64_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = l_Lean_instHashableMVarId_hash(v_x_1149_);
v___x_1152_ = lean_uint64_to_usize(v___x_1151_);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1148_, v___x_1152_, v___x_1153_, v_x_1149_, v_x_1150_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(lean_object* v_mvarId_1155_, lean_object* v_val_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v_mctx_1160_; lean_object* v_cache_1161_; lean_object* v_zetaDeltaFVarIds_1162_; lean_object* v_postponed_1163_; lean_object* v_diag_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1193_; 
v___x_1159_ = lean_st_ref_take(v___y_1157_);
v_mctx_1160_ = lean_ctor_get(v___x_1159_, 0);
v_cache_1161_ = lean_ctor_get(v___x_1159_, 1);
v_zetaDeltaFVarIds_1162_ = lean_ctor_get(v___x_1159_, 2);
v_postponed_1163_ = lean_ctor_get(v___x_1159_, 3);
v_diag_1164_ = lean_ctor_get(v___x_1159_, 4);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1166_ = v___x_1159_;
v_isShared_1167_ = v_isSharedCheck_1193_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_diag_1164_);
lean_inc(v_postponed_1163_);
lean_inc(v_zetaDeltaFVarIds_1162_);
lean_inc(v_cache_1161_);
lean_inc(v_mctx_1160_);
lean_dec(v___x_1159_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1193_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_depth_1168_; lean_object* v_levelAssignDepth_1169_; lean_object* v_lmvarCounter_1170_; lean_object* v_mvarCounter_1171_; lean_object* v_lDecls_1172_; lean_object* v_decls_1173_; lean_object* v_userNames_1174_; lean_object* v_lAssignment_1175_; lean_object* v_eAssignment_1176_; lean_object* v_dAssignment_1177_; lean_object* v_instanceTypedMVars_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1192_; 
v_depth_1168_ = lean_ctor_get(v_mctx_1160_, 0);
v_levelAssignDepth_1169_ = lean_ctor_get(v_mctx_1160_, 1);
v_lmvarCounter_1170_ = lean_ctor_get(v_mctx_1160_, 2);
v_mvarCounter_1171_ = lean_ctor_get(v_mctx_1160_, 3);
v_lDecls_1172_ = lean_ctor_get(v_mctx_1160_, 4);
v_decls_1173_ = lean_ctor_get(v_mctx_1160_, 5);
v_userNames_1174_ = lean_ctor_get(v_mctx_1160_, 6);
v_lAssignment_1175_ = lean_ctor_get(v_mctx_1160_, 7);
v_eAssignment_1176_ = lean_ctor_get(v_mctx_1160_, 8);
v_dAssignment_1177_ = lean_ctor_get(v_mctx_1160_, 9);
v_instanceTypedMVars_1178_ = lean_ctor_get(v_mctx_1160_, 10);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_mctx_1160_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1180_ = v_mctx_1160_;
v_isShared_1181_ = v_isSharedCheck_1192_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_instanceTypedMVars_1178_);
lean_inc(v_dAssignment_1177_);
lean_inc(v_eAssignment_1176_);
lean_inc(v_lAssignment_1175_);
lean_inc(v_userNames_1174_);
lean_inc(v_decls_1173_);
lean_inc(v_lDecls_1172_);
lean_inc(v_mvarCounter_1171_);
lean_inc(v_lmvarCounter_1170_);
lean_inc(v_levelAssignDepth_1169_);
lean_inc(v_depth_1168_);
lean_dec(v_mctx_1160_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1192_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_eAssignment_1176_, v_mvarId_1155_, v_val_1156_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 8, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_depth_1168_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_levelAssignDepth_1169_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_lmvarCounter_1170_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_mvarCounter_1171_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_lDecls_1172_);
lean_ctor_set(v_reuseFailAlloc_1191_, 5, v_decls_1173_);
lean_ctor_set(v_reuseFailAlloc_1191_, 6, v_userNames_1174_);
lean_ctor_set(v_reuseFailAlloc_1191_, 7, v_lAssignment_1175_);
lean_ctor_set(v_reuseFailAlloc_1191_, 8, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1191_, 9, v_dAssignment_1177_);
lean_ctor_set(v_reuseFailAlloc_1191_, 10, v_instanceTypedMVars_1178_);
v___x_1185_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1185_);
v___x_1187_ = v___x_1166_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_cache_1161_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_zetaDeltaFVarIds_1162_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_postponed_1163_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_diag_1164_);
v___x_1187_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_st_ref_put(v___y_1157_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1182_);
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg___boxed(lean_object* v_mvarId_1194_, lean_object* v_val_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1194_, v_val_1195_, v___y_1196_);
lean_dec(v___y_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_ref_1205_; lean_object* v___x_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_ref_1205_ = lean_ctor_get(v___y_1202_, 2);
v___x_1206_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_inc(v_ref_1205_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_ref_1205_);
lean_ctor_set(v___x_1211_, 1, v_a_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg___boxed(lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(lean_object* v_k_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1234_ = lean_apply_10(v_k_1223_, v_b_1228_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, lean_box(0));
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_k_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(v_k_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(lean_object* v_name_1247_, uint8_t v_bi_1248_, lean_object* v_type_1249_, lean_object* v_k_1250_, uint8_t v_kind_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; 
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1261_, 0, v_k_1250_);
lean_closure_set(v___f_1261_, 1, v___y_1252_);
lean_closure_set(v___f_1261_, 2, v___y_1253_);
lean_closure_set(v___f_1261_, 3, v___y_1254_);
lean_closure_set(v___f_1261_, 4, v___y_1255_);
v___x_1262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1247_, v_bi_1248_, v_type_1249_, v___f_1261_, v_kind_1251_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
return v___x_1262_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_name_1271_, lean_object* v_bi_1272_, lean_object* v_type_1273_, lean_object* v_k_1274_, lean_object* v_kind_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_bi_boxed_1285_; uint8_t v_kind_boxed_1286_; lean_object* v_res_1287_; 
v_bi_boxed_1285_ = lean_unbox(v_bi_1272_);
v_kind_boxed_1286_ = lean_unbox(v_kind_1275_);
v_res_1287_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1271_, v_bi_boxed_1285_, v_type_1273_, v_k_1274_, v_kind_boxed_1286_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(lean_object* v_name_1288_, lean_object* v_type_1289_, lean_object* v_k_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v___x_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = 0;
v___x_1301_ = 0;
v___x_1302_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1288_, v___x_1300_, v_type_1289_, v_k_1290_, v___x_1301_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg___boxed(lean_object* v_name_1303_, lean_object* v_type_1304_, lean_object* v_k_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1303_, v_type_1304_, v_k_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(lean_object* v_kSuccess_1316_, lean_object* v_a_1317_, lean_object* v_goal_1318_, uint8_t v_a_1319_, uint8_t v___x_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v_00_u03c3s_1326_, lean_object* v_hyps_1327_, lean_object* v_a_1328_, lean_object* v_target_1329_, lean_object* v_a_1330_, lean_object* v_h_u03c6_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc_ref(v_h_u03c6_1331_);
lean_inc_ref(v_a_1317_);
v___x_1341_ = lean_apply_12(v_kSuccess_1316_, v_a_1317_, v_h_u03c6_1331_, v_goal_1318_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_array_push(v___x_1344_, v_h_u03c6_1331_);
v___x_1346_ = 1;
v___x_1347_ = l_Lean_Meta_mkLambdaFVars(v___x_1345_, v_a_1342_, v_a_1319_, v___x_1320_, v_a_1319_, v___x_1320_, v___x_1346_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1360_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v_prf_1356_; lean_object* v___x_1358_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_1353_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_1354_ = l_Lean_Name_mkStr6(v___x_1321_, v___x_1322_, v___x_1323_, v___x_1324_, v___x_1352_, v___x_1353_);
v___x_1355_ = l_Lean_mkConst(v___x_1354_, v___x_1325_);
v_prf_1356_ = l_Lean_mkApp7(v___x_1355_, v_00_u03c3s_1326_, v_hyps_1327_, v_a_1328_, v_target_1329_, v_a_1317_, v_a_1330_, v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_prf_1356_);
v___x_1358_ = v___x_1350_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_prf_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_dec_ref(v_a_1330_);
lean_dec_ref(v_target_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_hyps_1327_);
lean_dec_ref(v_00_u03c3s_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v___x_1323_);
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_a_1317_);
return v___x_1347_;
}
}
else
{
lean_dec_ref(v_h_u03c6_1331_);
lean_dec_ref(v_a_1330_);
lean_dec_ref(v_target_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_hyps_1327_);
lean_dec_ref(v_00_u03c3s_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v___x_1323_);
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_a_1317_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed(lean_object** _args){
lean_object* v_kSuccess_1361_ = _args[0];
lean_object* v_a_1362_ = _args[1];
lean_object* v_goal_1363_ = _args[2];
lean_object* v_a_1364_ = _args[3];
lean_object* v___x_1365_ = _args[4];
lean_object* v___x_1366_ = _args[5];
lean_object* v___x_1367_ = _args[6];
lean_object* v___x_1368_ = _args[7];
lean_object* v___x_1369_ = _args[8];
lean_object* v___x_1370_ = _args[9];
lean_object* v_00_u03c3s_1371_ = _args[10];
lean_object* v_hyps_1372_ = _args[11];
lean_object* v_a_1373_ = _args[12];
lean_object* v_target_1374_ = _args[13];
lean_object* v_a_1375_ = _args[14];
lean_object* v_h_u03c6_1376_ = _args[15];
lean_object* v___y_1377_ = _args[16];
lean_object* v___y_1378_ = _args[17];
lean_object* v___y_1379_ = _args[18];
lean_object* v___y_1380_ = _args[19];
lean_object* v___y_1381_ = _args[20];
lean_object* v___y_1382_ = _args[21];
lean_object* v___y_1383_ = _args[22];
lean_object* v___y_1384_ = _args[23];
lean_object* v___y_1385_ = _args[24];
_start:
{
uint8_t v_a_11313__boxed_1386_; uint8_t v___x_11314__boxed_1387_; lean_object* v_res_1388_; 
v_a_11313__boxed_1386_ = lean_unbox(v_a_1364_);
v___x_11314__boxed_1387_ = lean_unbox(v___x_1365_);
v_res_1388_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(v_kSuccess_1361_, v_a_1362_, v_goal_1363_, v_a_11313__boxed_1386_, v___x_11314__boxed_1387_, v___x_1366_, v___x_1367_, v___x_1368_, v___x_1369_, v___x_1370_, v_00_u03c3s_1371_, v_hyps_1372_, v_a_1373_, v_target_1374_, v_a_1375_, v_h_u03c6_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1));
v___x_1397_ = l_Lean_mkConst(v___x_1396_, v___x_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(lean_object* v_goal_1398_, lean_object* v_kFail_1399_, lean_object* v_kSuccess_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_u_1410_; lean_object* v_00_u03c3s_1411_; lean_object* v_hyps_1412_; lean_object* v_target_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1489_; 
v_u_1410_ = lean_ctor_get(v_goal_1398_, 0);
v_00_u03c3s_1411_ = lean_ctor_get(v_goal_1398_, 1);
v_hyps_1412_ = lean_ctor_get(v_goal_1398_, 2);
v_target_1413_ = lean_ctor_get(v_goal_1398_, 3);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_goal_1398_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1415_ = v_goal_1398_;
v_isShared_1416_ = v_isSharedCheck_1489_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_target_1413_);
lean_inc(v_hyps_1412_);
lean_inc(v_00_u03c3s_1411_);
lean_inc(v_u_1410_);
lean_dec(v_goal_1398_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1489_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1);
v___x_1418_ = 0;
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_Meta_mkFreshExprMVar(v___x_1417_, v___x_1418_, v___x_1419_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1488_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1488_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1488_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0));
v___x_1426_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1));
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2));
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3));
v___x_1429_ = lean_box(0);
lean_inc(v_u_1410_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_u_1410_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc_ref(v___x_1430_);
v___x_1431_ = l_Lean_mkConst(v___x_1428_, v___x_1430_);
lean_inc_ref(v_00_u03c3s_1411_);
v___x_1432_ = l_Lean_Expr_app___override(v___x_1431_, v_00_u03c3s_1411_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 1);
lean_ctor_set(v___x_1423_, 0, v___x_1432_);
v___x_1434_ = v___x_1423_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Meta_mkFreshExprMVar(v___x_1434_, v___x_1418_, v___x_1419_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc_n(v_a_1436_, 2);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
v___x_1438_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0));
lean_inc_ref(v___x_1430_);
v___x_1439_ = l_Lean_mkConst(v___x_1438_, v___x_1430_);
lean_inc(v_a_1421_);
lean_inc_ref(v_hyps_1412_);
lean_inc_ref(v_00_u03c3s_1411_);
v___x_1440_ = l_Lean_mkApp4(v___x_1439_, v_00_u03c3s_1411_, v_hyps_1412_, v_a_1436_, v_a_1421_);
v___x_1441_ = lean_box(0);
v___x_1442_ = l_Lean_Meta_trySynthInstance(v___x_1440_, v___x_1441_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
if (lean_obj_tag(v_a_1443_) == 1)
{
lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_a_1444_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v_a_1443_, 1);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1);
lean_inc(v_a_1421_);
v___x_1446_ = l_Lean_Meta_isExprDefEq(v___x_1445_, v_a_1421_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; uint8_t v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = lean_unbox(v_a_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v_kFail_1399_);
v___x_1449_ = 1;
lean_inc_ref(v_hyps_1412_);
v___x_1450_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_hyps_1412_, v_a_1436_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v_goal_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_n(v_a_1451_, 2);
lean_dec_ref_known(v___x_1450_, 1);
lean_inc_ref(v_target_1413_);
lean_inc_ref(v_00_u03c3s_1411_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 2, v_a_1451_);
v_goal_1453_ = v___x_1415_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_u_1410_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_00_u03c3s_1411_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_a_1451_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_target_1413_);
v_goal_1453_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = lean_box(v___x_1449_);
lean_inc(v_a_1421_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed), 25, 15);
lean_closure_set(v___f_1455_, 0, v_kSuccess_1400_);
lean_closure_set(v___f_1455_, 1, v_a_1421_);
lean_closure_set(v___f_1455_, 2, v_goal_1453_);
lean_closure_set(v___f_1455_, 3, v_a_1447_);
lean_closure_set(v___f_1455_, 4, v___x_1454_);
lean_closure_set(v___f_1455_, 5, v___x_1425_);
lean_closure_set(v___f_1455_, 6, v___x_1426_);
lean_closure_set(v___f_1455_, 7, v___x_1427_);
lean_closure_set(v___f_1455_, 8, v___x_1437_);
lean_closure_set(v___f_1455_, 9, v___x_1430_);
lean_closure_set(v___f_1455_, 10, v_00_u03c3s_1411_);
lean_closure_set(v___f_1455_, 11, v_hyps_1412_);
lean_closure_set(v___f_1455_, 12, v_a_1451_);
lean_closure_set(v___f_1455_, 13, v_target_1413_);
lean_closure_set(v___f_1455_, 14, v_a_1444_);
v___x_1456_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_1457_ = l_Lean_Core_mkFreshUserName(v___x_1456_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_a_1458_, v_a_1421_, v___f_1455_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1459_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___f_1455_);
lean_dec(v_a_1421_);
v_a_1460_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1457_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_dec(v_a_1447_);
lean_dec(v_a_1444_);
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
return v___x_1450_;
}
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_a_1447_);
lean_dec(v_a_1444_);
lean_dec(v_a_1436_);
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
v___x_1469_ = lean_apply_9(v_kFail_1399_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
return v___x_1469_;
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1444_);
lean_dec(v_a_1436_);
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_dec_ref(v_kFail_1399_);
v_a_1470_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1446_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1446_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_a_1443_);
lean_dec(v_a_1436_);
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
v___x_1478_ = lean_apply_9(v_kFail_1399_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
return v___x_1478_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1436_);
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_dec_ref(v_kFail_1399_);
v_a_1479_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1442_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1442_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1430_, 2);
lean_dec(v_a_1421_);
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_dec_ref(v_kFail_1399_);
return v___x_1435_;
}
}
}
}
else
{
lean_del_object(v___x_1415_);
lean_dec_ref(v_target_1413_);
lean_dec_ref(v_hyps_1412_);
lean_dec_ref(v_00_u03c3s_1411_);
lean_dec(v_u_1410_);
lean_dec_ref(v_kSuccess_1400_);
lean_dec_ref(v_kFail_1399_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___boxed(lean_object* v_goal_1490_, lean_object* v_kFail_1491_, lean_object* v_kSuccess_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_goal_1490_, v_kFail_1491_, v_kSuccess_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1502_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(lean_object* v_a_1506_, lean_object* v___f_1507_, lean_object* v___f_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
lean_inc(v_a_1506_);
v___x_1518_ = l_Lean_MVarId_getType(v_a_1506_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_a_1519_, v___y_1514_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1521_);
lean_dec(v_a_1521_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v_val_1523_; lean_object* v___x_1524_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_val_1523_, v___f_1507_, v___f_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_a_1506_, v_a_1525_, v___y_1514_);
return v___x_1526_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1506_);
v_a_1527_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1524_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1524_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v___x_1522_);
lean_dec_ref(v___f_1508_);
lean_dec_ref(v___f_1507_);
lean_dec(v_a_1506_);
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1);
v___x_1536_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v___x_1535_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1536_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v___f_1508_);
lean_dec_ref(v___f_1507_);
lean_dec(v_a_1506_);
v_a_1537_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1518_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1518_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed(lean_object* v_a_1545_, lean_object* v___f_1546_, lean_object* v___f_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(v_a_1545_, v___f_1546_, v___f_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; 
v___f_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0));
v___f_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1));
v___x_1571_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1561_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_n(v_a_1572_, 2);
lean_dec_ref_known(v___x_1571_, 1);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1573_, 0, v_a_1572_);
lean_closure_set(v___f_1573_, 1, v___f_1569_);
lean_closure_set(v___f_1573_, 2, v___f_1570_);
v___x_1574_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_a_1572_, v___f_1573_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1571_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1571_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___boxed(lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(lean_object* v_x_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed(lean_object* v_x_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(v_x_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_x_1604_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(lean_object* v_00_u03b1_1615_, lean_object* v_msg_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_1616_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(v_00_u03b1_1626_, v_msg_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(lean_object* v_mvarId_1637_, lean_object* v_val_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1637_, v_val_1638_, v___y_1644_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___boxed(lean_object* v_mvarId_1649_, lean_object* v_val_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(v_mvarId_1649_, v_val_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(lean_object* v_00_u03b1_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1662_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(v_00_u03b1_1673_, v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1685_, lean_object* v_name_1686_, uint8_t v_bi_1687_, lean_object* v_type_1688_, lean_object* v_k_1689_, uint8_t v_kind_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1686_, v_bi_1687_, v_type_1688_, v_k_1689_, v_kind_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_name_1702_, lean_object* v_bi_1703_, lean_object* v_type_1704_, lean_object* v_k_1705_, lean_object* v_kind_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v_bi_boxed_1716_; uint8_t v_kind_boxed_1717_; lean_object* v_res_1718_; 
v_bi_boxed_1716_ = lean_unbox(v_bi_1703_);
v_kind_boxed_1717_ = lean_unbox(v_kind_1706_);
v_res_1718_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(v_00_u03b1_1701_, v_name_1702_, v_bi_boxed_1716_, v_type_1704_, v_k_1705_, v_kind_boxed_1717_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(lean_object* v_00_u03b1_1719_, lean_object* v_name_1720_, lean_object* v_type_1721_, lean_object* v_k_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1720_, v_type_1721_, v_k_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_name_1734_, lean_object* v_type_1735_, lean_object* v_k_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(v_00_u03b1_1733_, v_name_1734_, v_type_1735_, v_k_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5(lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_x_1748_, v_x_1749_, v_x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1752_, lean_object* v_x_1753_, size_t v_x_1754_, size_t v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1753_, v_x_1754_, v_x_1755_, v_x_1756_, v_x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
size_t v_x_11931__boxed_1765_; size_t v_x_11932__boxed_1766_; lean_object* v_res_1767_; 
v_x_11931__boxed_1765_ = lean_unbox_usize(v_x_1761_);
lean_dec(v_x_1761_);
v_x_11932__boxed_1766_ = lean_unbox_usize(v_x_1762_);
lean_dec(v_x_1762_);
v_res_1767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(v_00_u03b2_1759_, v_x_1760_, v_x_11931__boxed_1765_, v_x_11932__boxed_1766_, v_x_1763_, v_x_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1768_, lean_object* v_n_1769_, lean_object* v_k_1770_, lean_object* v_v_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v_n_1769_, v_k_1770_, v_v_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1773_, size_t v_depth_1774_, lean_object* v_keys_1775_, lean_object* v_vals_1776_, lean_object* v_heq_1777_, lean_object* v_i_1778_, lean_object* v_entries_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_1774_, v_keys_1775_, v_vals_1776_, v_i_1778_, v_entries_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_depth_1782_, lean_object* v_keys_1783_, lean_object* v_vals_1784_, lean_object* v_heq_1785_, lean_object* v_i_1786_, lean_object* v_entries_1787_){
_start:
{
size_t v_depth_boxed_1788_; lean_object* v_res_1789_; 
v_depth_boxed_1788_ = lean_unbox_usize(v_depth_1782_);
lean_dec(v_depth_1782_);
v_res_1789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_1781_, v_depth_boxed_1788_, v_keys_1783_, v_vals_1784_, v_heq_1785_, v_i_1786_, v_entries_1787_);
lean_dec_ref(v_vals_1784_);
lean_dec_ref(v_keys_1783_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_x_1791_, v_x_1792_, v_x_1793_, v_x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1(){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1815_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3));
v___x_1817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7));
v___x_1818_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed), 10, 0);
v___x_1819_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1815_, v___x_1816_, v___x_1817_, v___x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___boxed(lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
return v_res_1821_;
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
