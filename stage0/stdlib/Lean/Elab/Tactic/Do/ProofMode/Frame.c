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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_16_; lean_object* v_ngen_17_; lean_object* v_namePrefix_18_; lean_object* v_idx_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_48_; 
v___x_16_ = lean_st_ref_get(v___y_14_);
v_ngen_17_ = lean_ctor_get(v___x_16_, 2);
lean_inc_ref(v_ngen_17_);
lean_dec(v___x_16_);
v_namePrefix_18_ = lean_ctor_get(v_ngen_17_, 0);
v_idx_19_ = lean_ctor_get(v_ngen_17_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_ngen_17_);
if (v_isSharedCheck_48_ == 0)
{
v___x_21_ = v_ngen_17_;
v_isShared_22_ = v_isSharedCheck_48_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_idx_19_);
lean_inc(v_namePrefix_18_);
lean_dec(v_ngen_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_48_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v_env_24_; lean_object* v_nextMacroScope_25_; lean_object* v_auxDeclNGen_26_; lean_object* v_traceState_27_; lean_object* v_cache_28_; lean_object* v_messages_29_; lean_object* v_infoState_30_; lean_object* v_snapshotTasks_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_46_; 
v___x_23_ = lean_st_ref_take(v___y_14_);
v_env_24_ = lean_ctor_get(v___x_23_, 0);
v_nextMacroScope_25_ = lean_ctor_get(v___x_23_, 1);
v_auxDeclNGen_26_ = lean_ctor_get(v___x_23_, 3);
v_traceState_27_ = lean_ctor_get(v___x_23_, 4);
v_cache_28_ = lean_ctor_get(v___x_23_, 5);
v_messages_29_ = lean_ctor_get(v___x_23_, 6);
v_infoState_30_ = lean_ctor_get(v___x_23_, 7);
v_snapshotTasks_31_ = lean_ctor_get(v___x_23_, 8);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; 
v_unused_47_ = lean_ctor_get(v___x_23_, 2);
lean_dec(v_unused_47_);
v___x_33_ = v___x_23_;
v_isShared_34_ = v_isSharedCheck_46_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_snapshotTasks_31_);
lean_inc(v_infoState_30_);
lean_inc(v_messages_29_);
lean_inc(v_cache_28_);
lean_inc(v_traceState_27_);
lean_inc(v_auxDeclNGen_26_);
lean_inc(v_nextMacroScope_25_);
lean_inc(v_env_24_);
lean_dec(v___x_23_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_46_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v_r_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
lean_inc(v_idx_19_);
lean_inc(v_namePrefix_18_);
v_r_35_ = l_Lean_Name_num___override(v_namePrefix_18_, v_idx_19_);
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v_idx_19_, v___x_36_);
lean_dec(v_idx_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_37_);
v___x_39_ = v___x_21_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_namePrefix_18_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_45_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_41_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 2, v___x_39_);
v___x_41_ = v___x_33_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_env_24_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_nextMacroScope_25_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_auxDeclNGen_26_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_traceState_27_);
lean_ctor_set(v_reuseFailAlloc_44_, 5, v_cache_28_);
lean_ctor_set(v_reuseFailAlloc_44_, 6, v_messages_29_);
lean_ctor_set(v_reuseFailAlloc_44_, 7, v_infoState_30_);
lean_ctor_set(v_reuseFailAlloc_44_, 8, v_snapshotTasks_31_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_st_ref_set(v___y_14_, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_r_35_);
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg___boxed(lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_49_);
lean_dec(v___y_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___boxed(lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(lean_object* v_msg_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___f_71_; lean_object* v___x_3140__overap_72_; lean_object* v___x_73_; 
v___f_71_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0));
v___x_3140__overap_72_ = lean_panic_fn_borrowed(v___f_71_, v_msg_65_);
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
lean_inc(v___y_67_);
lean_inc_ref(v___y_66_);
v___x_73_ = lean_apply_5(v___x_3140__overap_72_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, lean_box(0));
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___boxed(lean_object* v_msg_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v_msg_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(lean_object* v_a_84_, lean_object* v_Ps_85_, lean_object* v_a_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_93_ = l_Lean_Core_mkFreshUserName(v___x_92_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_90_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_162_; 
v_snd_96_ = lean_ctor_get(v_a_86_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_163_);
v___x_98_ = v_a_86_;
v_isShared_99_ = v_isSharedCheck_162_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_dec(v_a_86_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_162_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_snd_96_) == 1)
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_146_; 
lean_dec_ref_known(v___x_95_, 1);
lean_dec(v_a_94_);
v_head_100_ = lean_ctor_get(v_snd_96_, 0);
v_tail_101_ = lean_ctor_get(v_snd_96_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_snd_96_);
if (v_isSharedCheck_146_ == 0)
{
v___x_103_ = v_snd_96_;
v_isShared_104_ = v_isSharedCheck_146_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_head_100_);
lean_dec(v_snd_96_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_146_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_name_105_; lean_object* v_uniq_106_; lean_object* v_p_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_145_; 
v_name_105_ = lean_ctor_get(v_head_100_, 0);
v_uniq_106_ = lean_ctor_get(v_head_100_, 1);
v_p_107_ = lean_ctor_get(v_head_100_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v_head_100_);
if (v_isSharedCheck_145_ == 0)
{
v___x_109_ = v_head_100_;
v_isShared_110_ = v_isSharedCheck_145_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_p_107_);
lean_inc(v_uniq_106_);
lean_inc(v_name_105_);
lean_dec(v_head_100_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_145_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; 
lean_inc_ref(v_a_84_);
v___x_111_ = l_Lean_Meta_isExprDefEq(v_p_107_, v_a_84_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_136_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_136_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint8_t v___x_116_; 
v___x_116_ = lean_unbox(v_a_112_);
lean_dec(v_a_112_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_119_; 
lean_del_object(v___x_114_);
lean_del_object(v___x_109_);
lean_dec(v_uniq_106_);
lean_dec(v_name_105_);
lean_del_object(v___x_103_);
v___x_117_ = lean_box(0);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_tail_101_);
lean_ctor_set(v___x_98_, 0, v___x_117_);
v___x_119_ = v___x_98_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_tail_101_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v_a_86_ = v___x_119_;
goto _start;
}
}
else
{
lean_object* v___x_123_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 2, v_a_84_);
v___x_123_ = v___x_109_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_name_105_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_uniq_106_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_a_84_);
v___x_123_ = v_reuseFailAlloc_135_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_123_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_124_);
lean_ctor_set(v___x_98_, 0, v_Ps_85_);
v___x_126_ = v___x_98_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_Ps_85_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_134_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 0);
lean_ctor_set(v___x_103_, 0, v___x_127_);
v___x_129_ = v___x_103_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_tail_101_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_129_);
v___x_131_ = v___x_114_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_del_object(v___x_109_);
lean_dec(v_uniq_106_);
lean_dec(v_name_105_);
lean_del_object(v___x_103_);
lean_dec(v_tail_101_);
lean_del_object(v___x_98_);
lean_dec(v_Ps_85_);
lean_dec_ref(v_a_84_);
v_a_137_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_111_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_111_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_161_; 
v_a_147_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_161_ == 0)
{
v___x_149_ = v___x_95_;
v_isShared_150_ = v_isSharedCheck_161_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_95_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_161_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_a_94_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
lean_ctor_set(v___x_151_, 2, v_a_84_);
v___x_152_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_151_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_152_);
lean_ctor_set(v___x_98_, 0, v_Ps_85_);
v___x_154_ = v___x_98_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_Ps_85_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_160_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_snd_96_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_156_);
v___x_158_ = v___x_149_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_94_);
lean_dec_ref(v_a_86_);
lean_dec(v_Ps_85_);
lean_dec_ref(v_a_84_);
v_a_164_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_95_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_95_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec_ref(v_a_86_);
lean_dec(v_Ps_85_);
lean_dec_ref(v_a_84_);
v_a_172_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_93_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_93_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___boxed(lean_object* v_a_180_, lean_object* v_Ps_181_, lean_object* v_a_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_180_, v_Ps_181_, v_a_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2));
v___x_193_ = lean_unsigned_to_nat(8u);
v___x_194_ = lean_unsigned_to_nat(51u);
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1));
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0));
v___x_197_ = l_mkPanicMessageWithDecl(v___x_196_, v___x_195_, v___x_194_, v___x_193_, v___x_192_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(lean_object* v_Ps_198_, lean_object* v_P_x27_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_P_x27_199_, v_a_201_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_269_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_269_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_269_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_269_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; 
lean_inc(v_a_206_);
v___x_210_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_206_);
if (lean_obj_tag(v___x_210_) == 1)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref_known(v___x_210_, 1);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_Ps_198_);
lean_ctor_set(v___x_211_, 1, v_a_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v___x_210_);
lean_del_object(v___x_208_);
v___x_215_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_206_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v_val_216_; lean_object* v_snd_217_; lean_object* v_snd_218_; lean_object* v_fst_219_; lean_object* v_fst_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_223_; 
lean_dec(v_a_206_);
v_val_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_215_, 1);
v_snd_217_ = lean_ctor_get(v_val_216_, 1);
lean_inc(v_snd_217_);
v_snd_218_ = lean_ctor_get(v_snd_217_, 1);
lean_inc(v_snd_218_);
v_fst_219_ = lean_ctor_get(v_val_216_, 0);
lean_inc(v_fst_219_);
lean_dec(v_val_216_);
v_fst_220_ = lean_ctor_get(v_snd_217_, 0);
lean_inc(v_fst_220_);
lean_dec(v_snd_217_);
v_fst_221_ = lean_ctor_get(v_snd_218_, 0);
lean_inc(v_fst_221_);
v_snd_222_ = lean_ctor_get(v_snd_218_, 1);
lean_inc(v_snd_222_);
lean_dec(v_snd_218_);
v___x_223_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_198_, v_fst_221_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v_fst_225_ = lean_ctor_get(v_a_224_, 0);
lean_inc(v_fst_225_);
v_snd_226_ = lean_ctor_get(v_a_224_, 1);
lean_inc(v_snd_226_);
lean_dec(v_a_224_);
v___x_227_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_fst_225_, v_snd_222_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_245_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_245_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_244_; 
v_fst_232_ = lean_ctor_get(v_a_228_, 0);
v_snd_233_ = lean_ctor_get(v_a_228_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_a_228_);
if (v_isSharedCheck_244_ == 0)
{
v___x_235_ = v_a_228_;
v_isShared_236_ = v_isSharedCheck_244_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_snd_233_);
lean_inc(v_fst_232_);
lean_dec(v_a_228_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_244_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_219_, v_fst_220_, v_snd_226_, v_snd_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_239_);
v___x_241_ = v___x_230_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
else
{
lean_dec(v_snd_226_);
lean_dec(v_fst_220_);
lean_dec(v_fst_219_);
return v___x_227_;
}
}
else
{
lean_dec(v_snd_222_);
lean_dec(v_fst_220_);
lean_dec(v_fst_219_);
return v___x_223_;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_215_);
v___x_246_ = lean_box(0);
lean_inc(v_Ps_198_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_Ps_198_);
v___x_248_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_206_, v_Ps_198_, v___x_247_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_260_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_260_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_fst_253_; 
v_fst_253_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_fst_253_);
lean_dec(v_a_249_);
if (lean_obj_tag(v_fst_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_del_object(v___x_251_);
v___x_254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3);
v___x_255_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v___x_254_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
return v___x_255_;
}
else
{
lean_object* v_val_256_; lean_object* v___x_258_; 
v_val_256_ = lean_ctor_get(v_fst_253_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v_fst_253_, 1);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v_val_256_);
v___x_258_ = v___x_251_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_val_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_248_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_248_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_Ps_198_);
v_a_270_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_205_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_205_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___boxed(lean_object* v_Ps_278_, lean_object* v_P_x27_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_278_, v_P_x27_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(lean_object* v_a_286_, lean_object* v_Ps_287_, lean_object* v_inst_288_, lean_object* v_a_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_286_, v_Ps_287_, v_a_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___boxed(lean_object* v_a_296_, lean_object* v_Ps_297_, lean_object* v_inst_298_, lean_object* v_a_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(v_a_296_, v_Ps_297_, v_inst_298_, v_a_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(lean_object* v_P_306_, lean_object* v_P_x27_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_box(0);
v___x_314_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_P_306_, v___x_313_);
v___x_315_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v___x_314_, v_P_x27_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_snd_320_; lean_object* v___x_322_; 
v_snd_320_ = lean_ctor_get(v_a_316_, 1);
lean_inc(v_snd_320_);
lean_dec(v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_snd_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_snd_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_325_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_315_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed(lean_object* v_P_333_, lean_object* v_P_x27_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_P_333_, v_P_x27_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0(lean_object* v_toApplicative_343_, lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_00_u03c3s_349_, lean_object* v_hyps_350_, lean_object* v_P_x27_351_, lean_object* v_target_352_, lean_object* v_00_u03c6_353_, lean_object* v_a_354_, lean_object* v_prf_355_){
_start:
{
lean_object* v_toPure_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_prf_361_; lean_object* v___x_362_; 
v_toPure_356_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc(v_toPure_356_);
lean_dec_ref(v_toApplicative_343_);
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_359_ = l_Lean_Name_mkStr6(v___x_344_, v___x_345_, v___x_346_, v___x_347_, v___x_357_, v___x_358_);
v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_348_);
v_prf_361_ = l_Lean_mkApp7(v___x_360_, v_00_u03c3s_349_, v_hyps_350_, v_P_x27_351_, v_target_352_, v_00_u03c6_353_, v_a_354_, v_prf_355_);
v___x_362_ = lean_apply_2(v_toPure_356_, lean_box(0), v_prf_361_);
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
uint8_t v_____do__lift_503__boxed_389_; uint8_t v___x_504__boxed_390_; lean_object* v_res_391_; 
v_____do__lift_503__boxed_389_ = lean_unbox(v_____do__lift_383_);
v___x_504__boxed_390_ = lean_unbox(v___x_384_);
v_res_391_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(v_h_u03c6_382_, v_____do__lift_503__boxed_389_, v___x_504__boxed_390_, v_inst_385_, v_toBind_386_, v___f_387_, v_prf_388_);
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
uint8_t v_____do__lift_539__boxed_415_; uint8_t v___x_540__boxed_416_; lean_object* v_res_417_; 
v_____do__lift_539__boxed_415_ = lean_unbox(v_____do__lift_406_);
v___x_540__boxed_416_ = lean_unbox(v___x_407_);
v_res_417_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(v_____do__lift_539__boxed_415_, v___x_540__boxed_416_, v_inst_408_, v_toBind_409_, v___f_410_, v_kSuccess_411_, v_00_u03c6_412_, v_goal_413_, v_h_u03c6_414_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(lean_object* v_toApplicative_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_00_u03c3s_446_, lean_object* v_hyps_447_, lean_object* v_target_448_, lean_object* v_00_u03c6_449_, lean_object* v_a_450_, lean_object* v_u_451_, uint8_t v_____do__lift_452_, uint8_t v___x_453_, lean_object* v_inst_454_, lean_object* v_toBind_455_, lean_object* v_kSuccess_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_P_x27_459_){
_start:
{
lean_object* v___f_460_; lean_object* v_goal_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc_ref_n(v_00_u03c6_449_, 2);
lean_inc_ref(v_target_448_);
lean_inc_ref(v_P_x27_459_);
lean_inc_ref(v_00_u03c3s_446_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0), 13, 12);
lean_closure_set(v___f_460_, 0, v_toApplicative_440_);
lean_closure_set(v___f_460_, 1, v___x_441_);
lean_closure_set(v___f_460_, 2, v___x_442_);
lean_closure_set(v___f_460_, 3, v___x_443_);
lean_closure_set(v___f_460_, 4, v___x_444_);
lean_closure_set(v___f_460_, 5, v___x_445_);
lean_closure_set(v___f_460_, 6, v_00_u03c3s_446_);
lean_closure_set(v___f_460_, 7, v_hyps_447_);
lean_closure_set(v___f_460_, 8, v_P_x27_459_);
lean_closure_set(v___f_460_, 9, v_target_448_);
lean_closure_set(v___f_460_, 10, v_00_u03c6_449_);
lean_closure_set(v___f_460_, 11, v_a_450_);
v_goal_461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_461_, 0, v_u_451_);
lean_ctor_set(v_goal_461_, 1, v_00_u03c3s_446_);
lean_ctor_set(v_goal_461_, 2, v_P_x27_459_);
lean_ctor_set(v_goal_461_, 3, v_target_448_);
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
lean_closure_set(v___f_464_, 6, v_00_u03c6_449_);
lean_closure_set(v___f_464_, 7, v_goal_461_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_465_, 0, v_inst_457_);
lean_closure_set(v___f_465_, 1, v_inst_458_);
lean_closure_set(v___f_465_, 2, v_00_u03c6_449_);
lean_closure_set(v___f_465_, 3, v___f_464_);
v___f_466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0));
v___x_467_ = lean_apply_2(v_inst_454_, lean_box(0), v___f_466_);
v___x_468_ = lean_apply_4(v_toBind_455_, lean_box(0), lean_box(0), v___x_467_, v___f_465_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_toApplicative_469_ = _args[0];
lean_object* v___x_470_ = _args[1];
lean_object* v___x_471_ = _args[2];
lean_object* v___x_472_ = _args[3];
lean_object* v___x_473_ = _args[4];
lean_object* v___x_474_ = _args[5];
lean_object* v_00_u03c3s_475_ = _args[6];
lean_object* v_hyps_476_ = _args[7];
lean_object* v_target_477_ = _args[8];
lean_object* v_00_u03c6_478_ = _args[9];
lean_object* v_a_479_ = _args[10];
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
uint8_t v_____do__lift_604__boxed_489_; uint8_t v___x_605__boxed_490_; lean_object* v_res_491_; 
v_____do__lift_604__boxed_489_ = lean_unbox(v_____do__lift_481_);
v___x_605__boxed_490_ = lean_unbox(v___x_482_);
v_res_491_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(v_toApplicative_469_, v___x_470_, v___x_471_, v___x_472_, v___x_473_, v___x_474_, v_00_u03c3s_475_, v_hyps_476_, v_target_477_, v_00_u03c6_478_, v_a_479_, v_u_480_, v_____do__lift_604__boxed_489_, v___x_605__boxed_490_, v_inst_483_, v_toBind_484_, v_kSuccess_485_, v_inst_486_, v_inst_487_, v_P_x27_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(lean_object* v_toApplicative_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v_00_u03c3s_498_, lean_object* v_hyps_499_, lean_object* v_target_500_, lean_object* v_00_u03c6_501_, lean_object* v_a_502_, lean_object* v_u_503_, lean_object* v_inst_504_, lean_object* v_toBind_505_, lean_object* v_kSuccess_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_P_x27_509_, lean_object* v_kFail_510_, uint8_t v_____do__lift_511_){
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
lean_inc_ref(v_hyps_499_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed), 20, 19);
lean_closure_set(v___f_515_, 0, v_toApplicative_492_);
lean_closure_set(v___f_515_, 1, v___x_493_);
lean_closure_set(v___f_515_, 2, v___x_494_);
lean_closure_set(v___f_515_, 3, v___x_495_);
lean_closure_set(v___f_515_, 4, v___x_496_);
lean_closure_set(v___f_515_, 5, v___x_497_);
lean_closure_set(v___f_515_, 6, v_00_u03c3s_498_);
lean_closure_set(v___f_515_, 7, v_hyps_499_);
lean_closure_set(v___f_515_, 8, v_target_500_);
lean_closure_set(v___f_515_, 9, v_00_u03c6_501_);
lean_closure_set(v___f_515_, 10, v_a_502_);
lean_closure_set(v___f_515_, 11, v_u_503_);
lean_closure_set(v___f_515_, 12, v___x_513_);
lean_closure_set(v___f_515_, 13, v___x_514_);
lean_closure_set(v___f_515_, 14, v_inst_504_);
lean_closure_set(v___f_515_, 15, v_toBind_505_);
lean_closure_set(v___f_515_, 16, v_kSuccess_506_);
lean_closure_set(v___f_515_, 17, v_inst_507_);
lean_closure_set(v___f_515_, 18, v_inst_508_);
v___x_516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed), 7, 2);
lean_closure_set(v___x_516_, 0, v_hyps_499_);
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
lean_dec_ref(v_a_502_);
lean_dec_ref(v_00_u03c6_501_);
lean_dec_ref(v_target_500_);
lean_dec_ref(v_hyps_499_);
lean_dec_ref(v_00_u03c3s_498_);
lean_dec(v___x_497_);
lean_dec_ref(v___x_496_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec_ref(v___x_493_);
lean_dec_ref(v_toApplicative_492_);
lean_inc(v_kFail_510_);
return v_kFail_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_toApplicative_519_ = _args[0];
lean_object* v___x_520_ = _args[1];
lean_object* v___x_521_ = _args[2];
lean_object* v___x_522_ = _args[3];
lean_object* v___x_523_ = _args[4];
lean_object* v___x_524_ = _args[5];
lean_object* v_00_u03c3s_525_ = _args[6];
lean_object* v_hyps_526_ = _args[7];
lean_object* v_target_527_ = _args[8];
lean_object* v_00_u03c6_528_ = _args[9];
lean_object* v_a_529_ = _args[10];
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
uint8_t v_____do__lift_658__boxed_539_; lean_object* v_res_540_; 
v_____do__lift_658__boxed_539_ = lean_unbox(v_____do__lift_538_);
v_res_540_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(v_toApplicative_519_, v___x_520_, v___x_521_, v___x_522_, v___x_523_, v___x_524_, v_00_u03c3s_525_, v_hyps_526_, v_target_527_, v_00_u03c6_528_, v_a_529_, v_u_530_, v_inst_531_, v_toBind_532_, v_kSuccess_533_, v_inst_534_, v_inst_535_, v_P_x27_536_, v_kFail_537_, v_____do__lift_658__boxed_539_);
lean_dec(v_kFail_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(lean_object* v_toApplicative_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v_00_u03c3s_550_, lean_object* v_hyps_551_, lean_object* v_target_552_, lean_object* v_00_u03c6_553_, lean_object* v_u_554_, lean_object* v_inst_555_, lean_object* v_toBind_556_, lean_object* v_kSuccess_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_P_x27_560_, lean_object* v_kFail_561_, lean_object* v___x_562_, lean_object* v_____do__lift_563_){
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
lean_inc_ref(v_00_u03c6_553_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed), 20, 19);
lean_closure_set(v___f_565_, 0, v_toApplicative_544_);
lean_closure_set(v___f_565_, 1, v___x_545_);
lean_closure_set(v___f_565_, 2, v___x_546_);
lean_closure_set(v___f_565_, 3, v___x_547_);
lean_closure_set(v___f_565_, 4, v___x_548_);
lean_closure_set(v___f_565_, 5, v___x_549_);
lean_closure_set(v___f_565_, 6, v_00_u03c3s_550_);
lean_closure_set(v___f_565_, 7, v_hyps_551_);
lean_closure_set(v___f_565_, 8, v_target_552_);
lean_closure_set(v___f_565_, 9, v_00_u03c6_553_);
lean_closure_set(v___f_565_, 10, v_a_564_);
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
lean_closure_set(v___x_568_, 1, v_00_u03c6_553_);
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
lean_dec_ref(v_00_u03c6_553_);
lean_dec_ref(v_target_552_);
lean_dec_ref(v_hyps_551_);
lean_dec_ref(v_00_u03c3s_550_);
lean_dec(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_545_);
lean_dec_ref(v_toApplicative_544_);
return v_kFail_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_toApplicative_571_ = _args[0];
lean_object* v___x_572_ = _args[1];
lean_object* v___x_573_ = _args[2];
lean_object* v___x_574_ = _args[3];
lean_object* v___x_575_ = _args[4];
lean_object* v___x_576_ = _args[5];
lean_object* v_00_u03c3s_577_ = _args[6];
lean_object* v_hyps_578_ = _args[7];
lean_object* v_target_579_ = _args[8];
lean_object* v_00_u03c6_580_ = _args[9];
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
v_res_591_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(v_toApplicative_571_, v___x_572_, v___x_573_, v___x_574_, v___x_575_, v___x_576_, v_00_u03c3s_577_, v_hyps_578_, v_target_579_, v_00_u03c6_580_, v_u_581_, v_inst_582_, v_toBind_583_, v_kSuccess_584_, v_inst_585_, v_inst_586_, v_P_x27_587_, v_kFail_588_, v___x_589_, v_____do__lift_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(lean_object* v_toApplicative_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v_00_u03c3s_599_, lean_object* v_hyps_600_, lean_object* v_target_601_, lean_object* v_00_u03c6_602_, lean_object* v_u_603_, lean_object* v_inst_604_, lean_object* v_toBind_605_, lean_object* v_kSuccess_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_kFail_609_, lean_object* v___x_610_, lean_object* v_P_x27_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
lean_inc_ref(v_P_x27_611_);
lean_inc(v_toBind_605_);
lean_inc(v_inst_604_);
lean_inc_ref(v_00_u03c6_602_);
lean_inc_ref(v_hyps_600_);
lean_inc_ref(v_00_u03c3s_599_);
lean_inc(v___x_598_);
lean_inc_ref(v___x_597_);
lean_inc_ref(v___x_596_);
lean_inc_ref(v___x_595_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed), 20, 19);
lean_closure_set(v___f_613_, 0, v_toApplicative_594_);
lean_closure_set(v___f_613_, 1, v___x_595_);
lean_closure_set(v___f_613_, 2, v___x_596_);
lean_closure_set(v___f_613_, 3, v___x_597_);
lean_closure_set(v___f_613_, 4, v___x_612_);
lean_closure_set(v___f_613_, 5, v___x_598_);
lean_closure_set(v___f_613_, 6, v_00_u03c3s_599_);
lean_closure_set(v___f_613_, 7, v_hyps_600_);
lean_closure_set(v___f_613_, 8, v_target_601_);
lean_closure_set(v___f_613_, 9, v_00_u03c6_602_);
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
v___x_615_ = l_Lean_Name_mkStr5(v___x_595_, v___x_596_, v___x_597_, v___x_612_, v___x_614_);
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_598_);
v___x_617_ = l_Lean_mkApp4(v___x_616_, v_00_u03c3s_599_, v_hyps_600_, v_P_x27_611_, v_00_u03c6_602_);
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
lean_object* v_toApplicative_622_ = _args[0];
lean_object* v___x_623_ = _args[1];
lean_object* v___x_624_ = _args[2];
lean_object* v___x_625_ = _args[3];
lean_object* v___x_626_ = _args[4];
lean_object* v_00_u03c3s_627_ = _args[5];
lean_object* v_hyps_628_ = _args[6];
lean_object* v_target_629_ = _args[7];
lean_object* v_00_u03c6_630_ = _args[8];
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
v_res_640_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(v_toApplicative_622_, v___x_623_, v___x_624_, v___x_625_, v___x_626_, v_00_u03c3s_627_, v_hyps_628_, v_target_629_, v_00_u03c6_630_, v_u_631_, v_inst_632_, v_toBind_633_, v_kSuccess_634_, v_inst_635_, v_inst_636_, v_kFail_637_, v___x_638_, v_P_x27_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(lean_object* v_u_648_, lean_object* v_toApplicative_649_, lean_object* v_00_u03c3s_650_, lean_object* v_hyps_651_, lean_object* v_target_652_, lean_object* v_inst_653_, lean_object* v_toBind_654_, lean_object* v_kSuccess_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_kFail_658_, uint8_t v___x_659_, lean_object* v___x_660_, lean_object* v_00_u03c6_661_){
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
lean_inc_ref(v_00_u03c3s_650_);
lean_inc_ref(v___x_667_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed), 18, 17);
lean_closure_set(v___f_668_, 0, v_toApplicative_649_);
lean_closure_set(v___f_668_, 1, v___x_662_);
lean_closure_set(v___f_668_, 2, v___x_663_);
lean_closure_set(v___f_668_, 3, v___x_664_);
lean_closure_set(v___f_668_, 4, v___x_667_);
lean_closure_set(v___f_668_, 5, v_00_u03c3s_650_);
lean_closure_set(v___f_668_, 6, v_hyps_651_);
lean_closure_set(v___f_668_, 7, v_target_652_);
lean_closure_set(v___f_668_, 8, v_00_u03c6_661_);
lean_closure_set(v___f_668_, 9, v_u_648_);
lean_closure_set(v___f_668_, 10, v_inst_653_);
lean_closure_set(v___f_668_, 11, v_toBind_654_);
lean_closure_set(v___f_668_, 12, v_kSuccess_655_);
lean_closure_set(v___f_668_, 13, v_inst_656_);
lean_closure_set(v___f_668_, 14, v_inst_657_);
lean_closure_set(v___f_668_, 15, v_kFail_658_);
lean_closure_set(v___f_668_, 16, v___x_666_);
v___x_669_ = l_Lean_mkConst(v___x_665_, v___x_667_);
v___x_670_ = l_Lean_Expr_app___override(v___x_669_, v_00_u03c3s_650_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed(lean_object* v_u_676_, lean_object* v_toApplicative_677_, lean_object* v_00_u03c3s_678_, lean_object* v_hyps_679_, lean_object* v_target_680_, lean_object* v_inst_681_, lean_object* v_toBind_682_, lean_object* v_kSuccess_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_kFail_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v_00_u03c6_689_){
_start:
{
uint8_t v___x_813__boxed_690_; lean_object* v_res_691_; 
v___x_813__boxed_690_ = lean_unbox(v___x_687_);
v_res_691_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(v_u_676_, v_toApplicative_677_, v_00_u03c3s_678_, v_hyps_679_, v_target_680_, v_inst_681_, v_toBind_682_, v_kSuccess_683_, v_inst_684_, v_inst_685_, v_kFail_686_, v___x_813__boxed_690_, v___x_688_, v_00_u03c6_689_);
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
lean_object* v_u_707_; lean_object* v_00_u03c3s_708_; lean_object* v_hyps_709_; lean_object* v_target_710_; lean_object* v_toApplicative_711_; lean_object* v_toBind_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_u_707_ = lean_ctor_get(v_goal_704_, 0);
lean_inc(v_u_707_);
v_00_u03c3s_708_ = lean_ctor_get(v_goal_704_, 1);
lean_inc_ref(v_00_u03c3s_708_);
v_hyps_709_ = lean_ctor_get(v_goal_704_, 2);
lean_inc_ref(v_hyps_709_);
v_target_710_ = lean_ctor_get(v_goal_704_, 3);
lean_inc_ref(v_target_710_);
lean_dec_ref(v_goal_704_);
v_toApplicative_711_ = lean_ctor_get(v_inst_701_, 0);
lean_inc_ref(v_toApplicative_711_);
v_toBind_712_ = lean_ctor_get(v_inst_701_, 1);
lean_inc_n(v_toBind_712_, 2);
v___x_713_ = 0;
v___x_714_ = lean_box(0);
v___x_715_ = lean_box(v___x_713_);
lean_inc(v_inst_703_);
v___f_716_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed), 14, 13);
lean_closure_set(v___f_716_, 0, v_u_707_);
lean_closure_set(v___f_716_, 1, v_toApplicative_711_);
lean_closure_set(v___f_716_, 2, v_00_u03c3s_708_);
lean_closure_set(v___f_716_, 3, v_hyps_709_);
lean_closure_set(v___f_716_, 4, v_target_710_);
lean_closure_set(v___f_716_, 5, v_inst_703_);
lean_closure_set(v___f_716_, 6, v_toBind_712_);
lean_closure_set(v___f_716_, 7, v_kSuccess_706_);
lean_closure_set(v___f_716_, 8, v_inst_702_);
lean_closure_set(v___f_716_, 9, v_inst_701_);
lean_closure_set(v___f_716_, 10, v_kFail_705_);
lean_closure_set(v___f_716_, 11, v___x_715_);
lean_closure_set(v___f_716_, 12, v___x_714_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2);
v___x_718_ = lean_apply_2(v_inst_703_, lean_box(0), v___x_717_);
v___x_719_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_718_, v___f_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore(lean_object* v_m_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_goal_724_, lean_object* v_kFail_725_, lean_object* v_kSuccess_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_721_, v_inst_722_, v_inst_723_, v_goal_724_, v_kFail_725_, v_kSuccess_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(lean_object* v_k_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_goal_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_apply_1(v_k_728_, v_goal_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed(lean_object* v_k_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_goal_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(v_k_733_, v_x_734_, v_x_735_, v_goal_736_);
lean_dec_ref(v_x_735_);
lean_dec_ref(v_x_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_goal_741_, lean_object* v_k_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_inc(v_k_742_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_743_, 0, v_k_742_);
lean_inc_ref(v_goal_741_);
v___x_744_ = lean_apply_1(v_k_742_, v_goal_741_);
v___x_745_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(v_inst_738_, v_inst_739_, v_inst_740_, v_goal_741_, v___x_744_, v___f_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame(lean_object* v_m_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_goal_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(v_inst_747_, v_inst_748_, v_inst_749_, v_goal_750_, v_k_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(lean_object* v_e_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = l_Lean_Expr_hasMVar(v_e_753_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_e_753_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v_mctx_759_; lean_object* v___x_760_; lean_object* v_fst_761_; lean_object* v_snd_762_; lean_object* v___x_763_; lean_object* v_cache_764_; lean_object* v_zetaDeltaFVarIds_765_; lean_object* v_postponed_766_; lean_object* v_diag_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v___x_758_ = lean_st_ref_get(v___y_754_);
v_mctx_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_mctx_759_);
lean_dec(v___x_758_);
v___x_760_ = l_Lean_instantiateMVarsCore(v_mctx_759_, v_e_753_);
v_fst_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_fst_761_);
v_snd_762_ = lean_ctor_get(v___x_760_, 1);
lean_inc(v_snd_762_);
lean_dec_ref(v___x_760_);
v___x_763_ = lean_st_ref_take(v___y_754_);
v_cache_764_ = lean_ctor_get(v___x_763_, 1);
v_zetaDeltaFVarIds_765_ = lean_ctor_get(v___x_763_, 2);
v_postponed_766_ = lean_ctor_get(v___x_763_, 3);
v_diag_767_ = lean_ctor_get(v___x_763_, 4);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_763_, 0);
lean_dec(v_unused_777_);
v___x_769_ = v___x_763_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_diag_767_);
lean_inc(v_postponed_766_);
lean_inc(v_zetaDeltaFVarIds_765_);
lean_inc(v_cache_764_);
lean_dec(v___x_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_snd_762_);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_snd_762_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_cache_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_zetaDeltaFVarIds_765_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_postponed_766_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_diag_767_);
v___x_772_ = v_reuseFailAlloc_775_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_st_ref_set(v___y_754_, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_fst_761_);
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg___boxed(lean_object* v_e_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_778_, v___y_779_);
lean_dec(v___y_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(lean_object* v_e_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_e_782_, v___y_788_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___boxed(lean_object* v_e_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(v_e_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
v___x_814_ = lean_apply_9(v_x_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed(lean_object* v_x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(v_x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; 
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_837_, 0, v_x_827_);
lean_closure_set(v___f_837_, 1, v___y_828_);
lean_closure_set(v___f_837_, 2, v___y_829_);
lean_closure_set(v___f_837_, 3, v___y_830_);
lean_closure_set(v___f_837_, 4, v___y_831_);
v___x_838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_826_, v___f_837_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
return v___x_838_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___boxed(lean_object* v_mvarId_847_, lean_object* v_x_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_847_, v_x_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(lean_object* v_00_u03b1_859_, lean_object* v_mvarId_860_, lean_object* v_x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_860_, v_x_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___boxed(lean_object* v_00_u03b1_872_, lean_object* v_mvarId_873_, lean_object* v_x_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(v_00_u03b1_872_, v_mvarId_873_, v_x_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(lean_object* v_msgData_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_env_892_; lean_object* v___x_893_; lean_object* v_mctx_894_; lean_object* v_lctx_895_; lean_object* v_options_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_891_ = lean_st_ref_get(v___y_889_);
v_env_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_891_);
v___x_893_ = lean_st_ref_get(v___y_887_);
v_mctx_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc_ref(v_mctx_894_);
lean_dec(v___x_893_);
v_lctx_895_ = lean_ctor_get(v___y_886_, 2);
v_options_896_ = lean_ctor_get(v___y_888_, 2);
lean_inc_ref(v_options_896_);
lean_inc_ref(v_lctx_895_);
v___x_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_897_, 0, v_env_892_);
lean_ctor_set(v___x_897_, 1, v_mctx_894_);
lean_ctor_set(v___x_897_, 2, v_lctx_895_);
lean_ctor_set(v___x_897_, 3, v_options_896_);
v___x_898_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_msgData_885_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0___boxed(lean_object* v_msgData_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msgData_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_ref_913_; lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_ref_913_ = lean_ctor_get(v___y_910_, 5);
v___x_914_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_ref_913_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_ref_913_);
lean_ctor_set(v___x_919_, 1, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 1);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg___boxed(lean_object* v_msg_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_930_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1);
v___x_944_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v___x_943_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed(lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(v_x_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v_x_945_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_goal_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_957_);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_967_, v___x_968_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_Expr_mvarId_x21(v_a_970_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_973_, v___y_959_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_982_);
v___x_976_ = v___x_974_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_974_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_a_970_);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_970_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_970_);
v_a_983_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_974_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_974_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed(lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_goal_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(v_x_991_, v_x_992_, v_goal_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_x_992_);
lean_dec_ref(v_x_991_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_ks_1008_; lean_object* v_vs_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1033_; 
v_ks_1008_ = lean_ctor_get(v_x_1004_, 0);
v_vs_1009_ = lean_ctor_get(v_x_1004_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1011_ = v_x_1004_;
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_vs_1009_);
lean_inc(v_ks_1008_);
lean_dec(v_x_1004_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = lean_array_get_size(v_ks_1008_);
v___x_1014_ = lean_nat_dec_lt(v_x_1005_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_dec(v_x_1005_);
v___x_1015_ = lean_array_push(v_ks_1008_, v_x_1006_);
v___x_1016_ = lean_array_push(v_vs_1009_, v_x_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1016_);
lean_ctor_set(v___x_1011_, 0, v___x_1015_);
v___x_1018_ = v___x_1011_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
else
{
lean_object* v_k_x27_1020_; uint8_t v___x_1021_; 
v_k_x27_1020_ = lean_array_fget_borrowed(v_ks_1008_, v_x_1005_);
v___x_1021_ = l_Lean_instBEqMVarId_beq(v_x_1006_, v_k_x27_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1023_; 
if (v_isShared_1012_ == 0)
{
v___x_1023_ = v___x_1011_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_ks_1008_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_vs_1009_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_add(v_x_1005_, v___x_1024_);
lean_dec(v_x_1005_);
v_x_1004_ = v___x_1023_;
v_x_1005_ = v___x_1025_;
goto _start;
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1028_ = lean_array_fset(v_ks_1008_, v_x_1005_, v_x_1006_);
v___x_1029_ = lean_array_fset(v_vs_1009_, v_x_1005_, v_x_1007_);
lean_dec(v_x_1005_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1029_);
lean_ctor_set(v___x_1011_, 0, v___x_1028_);
v___x_1031_ = v___x_1011_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_n_1034_, lean_object* v_k_1035_, lean_object* v_v_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_n_1034_, v___x_1037_, v_k_1035_, v_v_1036_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(lean_object* v_x_1040_, size_t v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
if (lean_obj_tag(v_x_1040_) == 0)
{
lean_object* v_es_1045_; size_t v___x_1046_; size_t v___x_1047_; lean_object* v_j_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_es_1045_ = lean_ctor_get(v_x_1040_, 0);
v___x_1046_ = ((size_t)31ULL);
v___x_1047_ = lean_usize_land(v_x_1041_, v___x_1046_);
v_j_1048_ = lean_usize_to_nat(v___x_1047_);
v___x_1049_ = lean_array_get_size(v_es_1045_);
v___x_1050_ = lean_nat_dec_lt(v_j_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec(v_j_1048_);
lean_dec(v_x_1044_);
lean_dec(v_x_1043_);
return v_x_1040_;
}
else
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1089_; 
lean_inc_ref(v_es_1045_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1040_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_x_1040_, 0);
lean_dec(v_unused_1090_);
v___x_1052_ = v_x_1040_;
v_isShared_1053_ = v_isSharedCheck_1089_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v_x_1040_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1089_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_v_1054_; lean_object* v___x_1055_; lean_object* v_xs_x27_1056_; lean_object* v___y_1058_; 
v_v_1054_ = lean_array_fget(v_es_1045_, v_j_1048_);
v___x_1055_ = lean_box(0);
v_xs_x27_1056_ = lean_array_fset(v_es_1045_, v_j_1048_, v___x_1055_);
switch(lean_obj_tag(v_v_1054_))
{
case 0:
{
lean_object* v_key_1063_; lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1074_; 
v_key_1063_ = lean_ctor_get(v_v_1054_, 0);
v_val_1064_ = lean_ctor_get(v_v_1054_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_v_1054_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1066_ = v_v_1054_;
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_inc(v_key_1063_);
lean_dec(v_v_1054_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_instBEqMVarId_beq(v_x_1043_, v_key_1063_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_del_object(v___x_1066_);
v___x_1069_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1063_, v_val_1064_, v_x_1043_, v_x_1044_);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
v___y_1058_ = v___x_1070_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_val_1064_);
lean_dec(v_key_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_x_1044_);
lean_ctor_set(v___x_1066_, 0, v_x_1043_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_x_1043_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_x_1044_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v___y_1058_ = v___x_1072_;
goto v___jp_1057_;
}
}
}
}
case 1:
{
lean_object* v_node_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1087_; 
v_node_1075_ = lean_ctor_get(v_v_1054_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_v_1054_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1077_ = v_v_1054_;
v_isShared_1078_ = v_isSharedCheck_1087_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_node_1075_);
lean_dec(v_v_1054_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1087_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1079_ = ((size_t)5ULL);
v___x_1080_ = lean_usize_shift_right(v_x_1041_, v___x_1079_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_x_1042_, v___x_1081_);
v___x_1083_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_node_1075_, v___x_1080_, v___x_1082_, v_x_1043_, v_x_1044_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1083_);
v___x_1085_ = v___x_1077_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v___y_1058_ = v___x_1085_;
goto v___jp_1057_;
}
}
}
default: 
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_x_1043_);
lean_ctor_set(v___x_1088_, 1, v_x_1044_);
v___y_1058_ = v___x_1088_;
goto v___jp_1057_;
}
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_array_fset(v_xs_x27_1056_, v_j_1048_, v___y_1058_);
lean_dec(v_j_1048_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1059_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_ks_1091_; lean_object* v_vs_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1112_; 
v_ks_1091_ = lean_ctor_get(v_x_1040_, 0);
v_vs_1092_ = lean_ctor_get(v_x_1040_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1040_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1094_ = v_x_1040_;
v_isShared_1095_ = v_isSharedCheck_1112_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_vs_1092_);
lean_inc(v_ks_1091_);
lean_dec(v_x_1040_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1112_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_ks_1091_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_vs_1092_);
v___x_1097_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v_newNode_1098_; uint8_t v___y_1100_; size_t v___x_1106_; uint8_t v___x_1107_; 
v_newNode_1098_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v___x_1097_, v_x_1043_, v_x_1044_);
v___x_1106_ = ((size_t)7ULL);
v___x_1107_ = lean_usize_dec_le(v___x_1106_, v_x_1042_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1098_);
v___x_1109_ = lean_unsigned_to_nat(4u);
v___x_1110_ = lean_nat_dec_lt(v___x_1108_, v___x_1109_);
lean_dec(v___x_1108_);
v___y_1100_ = v___x_1110_;
goto v___jp_1099_;
}
else
{
v___y_1100_ = v___x_1107_;
goto v___jp_1099_;
}
v___jp_1099_:
{
if (v___y_1100_ == 0)
{
lean_object* v_ks_1101_; lean_object* v_vs_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_ks_1101_ = lean_ctor_get(v_newNode_1098_, 0);
lean_inc_ref(v_ks_1101_);
v_vs_1102_ = lean_ctor_get(v_newNode_1098_, 1);
lean_inc_ref(v_vs_1102_);
lean_dec_ref(v_newNode_1098_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0);
v___x_1105_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_x_1042_, v_ks_1101_, v_vs_1102_, v___x_1103_, v___x_1104_);
lean_dec_ref(v_vs_1102_);
lean_dec_ref(v_ks_1101_);
return v___x_1105_;
}
else
{
return v_newNode_1098_;
}
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
size_t v_x_10934__boxed_1145_; size_t v_x_10935__boxed_1146_; lean_object* v_res_1147_; 
v_x_10934__boxed_1145_ = lean_unbox_usize(v_x_1141_);
lean_dec(v_x_1141_);
v_x_10935__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1140_, v_x_10934__boxed_1145_, v_x_10935__boxed_1146_, v_x_1143_, v_x_1144_);
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
lean_object* v___x_1159_; lean_object* v_mctx_1160_; lean_object* v_cache_1161_; lean_object* v_zetaDeltaFVarIds_1162_; lean_object* v_postponed_1163_; lean_object* v_diag_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1192_; 
v___x_1159_ = lean_st_ref_take(v___y_1157_);
v_mctx_1160_ = lean_ctor_get(v___x_1159_, 0);
v_cache_1161_ = lean_ctor_get(v___x_1159_, 1);
v_zetaDeltaFVarIds_1162_ = lean_ctor_get(v___x_1159_, 2);
v_postponed_1163_ = lean_ctor_get(v___x_1159_, 3);
v_diag_1164_ = lean_ctor_get(v___x_1159_, 4);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1166_ = v___x_1159_;
v_isShared_1167_ = v_isSharedCheck_1192_;
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
v_isShared_1167_ = v_isSharedCheck_1192_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_depth_1168_; lean_object* v_levelAssignDepth_1169_; lean_object* v_lmvarCounter_1170_; lean_object* v_mvarCounter_1171_; lean_object* v_lDecls_1172_; lean_object* v_decls_1173_; lean_object* v_userNames_1174_; lean_object* v_lAssignment_1175_; lean_object* v_eAssignment_1176_; lean_object* v_dAssignment_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1191_; 
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
v_isSharedCheck_1191_ = !lean_is_exclusive(v_mctx_1160_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1179_ = v_mctx_1160_;
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
else
{
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
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_eAssignment_1176_, v_mvarId_1155_, v_val_1156_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 8, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_depth_1168_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_levelAssignDepth_1169_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_lmvarCounter_1170_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_mvarCounter_1171_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_lDecls_1172_);
lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_decls_1173_);
lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_userNames_1174_);
lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_lAssignment_1175_);
lean_ctor_set(v_reuseFailAlloc_1190_, 8, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1190_, 9, v_dAssignment_1177_);
v___x_1183_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1183_);
v___x_1185_ = v___x_1166_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_cache_1161_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_zetaDeltaFVarIds_1162_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_postponed_1163_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_diag_1164_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_st_ref_set(v___y_1157_, v___x_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg___boxed(lean_object* v_mvarId_1193_, lean_object* v_val_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1193_, v_val_1194_, v___y_1195_);
lean_dec(v___y_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(lean_object* v_msg_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_ref_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_ref_1204_ = lean_ctor_get(v___y_1201_, 5);
v___x_1205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_inc(v_ref_1204_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_ref_1204_);
lean_ctor_set(v___x_1210_, 1, v_a_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 1);
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg___boxed(lean_object* v_msg_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(lean_object* v_k_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1226_);
lean_inc_ref(v___y_1225_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
v___x_1233_ = lean_apply_10(v_k_1222_, v_b_1227_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, lean_box(0));
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_k_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(v_k_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v_b_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(lean_object* v_name_1246_, uint8_t v_bi_1247_, lean_object* v_type_1248_, lean_object* v_k_1249_, uint8_t v_kind_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___f_1260_; lean_object* v___x_1261_; 
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1260_, 0, v_k_1249_);
lean_closure_set(v___f_1260_, 1, v___y_1251_);
lean_closure_set(v___f_1260_, 2, v___y_1252_);
lean_closure_set(v___f_1260_, 3, v___y_1253_);
lean_closure_set(v___f_1260_, 4, v___y_1254_);
v___x_1261_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1246_, v_bi_1247_, v_type_1248_, v___f_1260_, v_kind_1250_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_name_1270_, lean_object* v_bi_1271_, lean_object* v_type_1272_, lean_object* v_k_1273_, lean_object* v_kind_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v_bi_boxed_1284_; uint8_t v_kind_boxed_1285_; lean_object* v_res_1286_; 
v_bi_boxed_1284_ = lean_unbox(v_bi_1271_);
v_kind_boxed_1285_ = lean_unbox(v_kind_1274_);
v_res_1286_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1270_, v_bi_boxed_1284_, v_type_1272_, v_k_1273_, v_kind_boxed_1285_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(lean_object* v_name_1287_, lean_object* v_type_1288_, lean_object* v_k_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = 0;
v___x_1300_ = 0;
v___x_1301_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1287_, v___x_1299_, v_type_1288_, v_k_1289_, v___x_1300_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg___boxed(lean_object* v_name_1302_, lean_object* v_type_1303_, lean_object* v_k_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1302_, v_type_1303_, v_k_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(lean_object* v_kSuccess_1315_, lean_object* v_a_1316_, lean_object* v_goal_1317_, uint8_t v_a_1318_, uint8_t v___x_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_00_u03c3s_1325_, lean_object* v_hyps_1326_, lean_object* v_a_1327_, lean_object* v_target_1328_, lean_object* v_a_1329_, lean_object* v_h_u03c6_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc_ref(v_h_u03c6_1330_);
lean_inc_ref(v_a_1316_);
v___x_1340_ = lean_apply_12(v_kSuccess_1315_, v_a_1316_, v_h_u03c6_1330_, v_goal_1317_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, lean_box(0));
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
v___x_1344_ = lean_array_push(v___x_1343_, v_h_u03c6_1330_);
v___x_1345_ = 1;
v___x_1346_ = l_Lean_Meta_mkLambdaFVars(v___x_1344_, v_a_1341_, v_a_1318_, v___x_1319_, v_a_1318_, v___x_1319_, v___x_1345_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___x_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1359_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1359_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_prf_1355_; lean_object* v___x_1357_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0));
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1));
v___x_1353_ = l_Lean_Name_mkStr6(v___x_1320_, v___x_1321_, v___x_1322_, v___x_1323_, v___x_1351_, v___x_1352_);
v___x_1354_ = l_Lean_mkConst(v___x_1353_, v___x_1324_);
v_prf_1355_ = l_Lean_mkApp7(v___x_1354_, v_00_u03c3s_1325_, v_hyps_1326_, v_a_1327_, v_target_1328_, v_a_1316_, v_a_1329_, v_a_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_prf_1355_);
v___x_1357_ = v___x_1349_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_prf_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_target_1328_);
lean_dec_ref(v_a_1327_);
lean_dec_ref(v_hyps_1326_);
lean_dec_ref(v_00_u03c3s_1325_);
lean_dec(v___x_1324_);
lean_dec_ref(v___x_1323_);
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_a_1316_);
return v___x_1346_;
}
}
else
{
lean_dec_ref(v_h_u03c6_1330_);
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_target_1328_);
lean_dec_ref(v_a_1327_);
lean_dec_ref(v_hyps_1326_);
lean_dec_ref(v_00_u03c3s_1325_);
lean_dec(v___x_1324_);
lean_dec_ref(v___x_1323_);
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_a_1316_);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed(lean_object** _args){
lean_object* v_kSuccess_1360_ = _args[0];
lean_object* v_a_1361_ = _args[1];
lean_object* v_goal_1362_ = _args[2];
lean_object* v_a_1363_ = _args[3];
lean_object* v___x_1364_ = _args[4];
lean_object* v___x_1365_ = _args[5];
lean_object* v___x_1366_ = _args[6];
lean_object* v___x_1367_ = _args[7];
lean_object* v___x_1368_ = _args[8];
lean_object* v___x_1369_ = _args[9];
lean_object* v_00_u03c3s_1370_ = _args[10];
lean_object* v_hyps_1371_ = _args[11];
lean_object* v_a_1372_ = _args[12];
lean_object* v_target_1373_ = _args[13];
lean_object* v_a_1374_ = _args[14];
lean_object* v_h_u03c6_1375_ = _args[15];
lean_object* v___y_1376_ = _args[16];
lean_object* v___y_1377_ = _args[17];
lean_object* v___y_1378_ = _args[18];
lean_object* v___y_1379_ = _args[19];
lean_object* v___y_1380_ = _args[20];
lean_object* v___y_1381_ = _args[21];
lean_object* v___y_1382_ = _args[22];
lean_object* v___y_1383_ = _args[23];
lean_object* v___y_1384_ = _args[24];
_start:
{
uint8_t v_a_11296__boxed_1385_; uint8_t v___x_11297__boxed_1386_; lean_object* v_res_1387_; 
v_a_11296__boxed_1385_ = lean_unbox(v_a_1363_);
v___x_11297__boxed_1386_ = lean_unbox(v___x_1364_);
v_res_1387_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(v_kSuccess_1360_, v_a_1361_, v_goal_1362_, v_a_11296__boxed_1385_, v___x_11297__boxed_1386_, v___x_1365_, v___x_1366_, v___x_1367_, v___x_1368_, v___x_1369_, v_00_u03c3s_1370_, v_hyps_1371_, v_a_1372_, v_target_1373_, v_a_1374_, v_h_u03c6_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1387_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1));
v___x_1396_ = l_Lean_mkConst(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(lean_object* v_goal_1397_, lean_object* v_kFail_1398_, lean_object* v_kSuccess_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_u_1409_; lean_object* v_00_u03c3s_1410_; lean_object* v_hyps_1411_; lean_object* v_target_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1488_; 
v_u_1409_ = lean_ctor_get(v_goal_1397_, 0);
v_00_u03c3s_1410_ = lean_ctor_get(v_goal_1397_, 1);
v_hyps_1411_ = lean_ctor_get(v_goal_1397_, 2);
v_target_1412_ = lean_ctor_get(v_goal_1397_, 3);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_goal_1397_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1414_ = v_goal_1397_;
v_isShared_1415_ = v_isSharedCheck_1488_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_target_1412_);
lean_inc(v_hyps_1411_);
lean_inc(v_00_u03c3s_1410_);
lean_inc(v_u_1409_);
lean_dec(v_goal_1397_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1488_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1);
v___x_1417_ = 0;
v___x_1418_ = lean_box(0);
v___x_1419_ = l_Lean_Meta_mkFreshExprMVar(v___x_1416_, v___x_1417_, v___x_1418_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1487_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1487_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1487_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1424_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0));
v___x_1425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1));
v___x_1426_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2));
v___x_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3));
v___x_1428_ = lean_box(0);
lean_inc(v_u_1409_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_u_1409_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc_ref(v___x_1429_);
v___x_1430_ = l_Lean_mkConst(v___x_1427_, v___x_1429_);
lean_inc_ref(v_00_u03c3s_1410_);
v___x_1431_ = l_Lean_Expr_app___override(v___x_1430_, v_00_u03c3s_1410_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1431_);
v___x_1433_ = v___x_1422_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Meta_mkFreshExprMVar(v___x_1433_, v___x_1417_, v___x_1418_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_n(v_a_1435_, 2);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0));
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0));
lean_inc_ref(v___x_1429_);
v___x_1438_ = l_Lean_mkConst(v___x_1437_, v___x_1429_);
lean_inc(v_a_1420_);
lean_inc_ref(v_hyps_1411_);
lean_inc_ref(v_00_u03c3s_1410_);
v___x_1439_ = l_Lean_mkApp4(v___x_1438_, v_00_u03c3s_1410_, v_hyps_1411_, v_a_1435_, v_a_1420_);
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Lean_Meta_trySynthInstance(v___x_1439_, v___x_1440_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
if (lean_obj_tag(v_a_1442_) == 1)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_a_1443_ = lean_ctor_get(v_a_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v_a_1442_, 1);
v___x_1444_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1);
lean_inc(v_a_1420_);
v___x_1445_ = l_Lean_Meta_isExprDefEq(v___x_1444_, v_a_1420_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; uint8_t v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = lean_unbox(v_a_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v_kFail_1398_);
lean_inc_ref(v_hyps_1411_);
v___x_1448_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(v_hyps_1411_, v_a_1435_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1));
v___x_1451_ = l_Lean_Core_mkFreshUserName(v___x_1450_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; uint8_t v___x_1453_; lean_object* v_goal_1455_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = 1;
lean_inc_ref(v_target_1412_);
lean_inc(v_a_1449_);
lean_inc_ref(v_00_u03c3s_1410_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 2, v_a_1449_);
v_goal_1455_ = v___x_1414_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_u_1409_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_00_u03c3s_1410_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_target_1412_);
v_goal_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(v___x_1453_);
lean_inc(v_a_1420_);
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed), 25, 15);
lean_closure_set(v___f_1457_, 0, v_kSuccess_1399_);
lean_closure_set(v___f_1457_, 1, v_a_1420_);
lean_closure_set(v___f_1457_, 2, v_goal_1455_);
lean_closure_set(v___f_1457_, 3, v_a_1446_);
lean_closure_set(v___f_1457_, 4, v___x_1456_);
lean_closure_set(v___f_1457_, 5, v___x_1424_);
lean_closure_set(v___f_1457_, 6, v___x_1425_);
lean_closure_set(v___f_1457_, 7, v___x_1426_);
lean_closure_set(v___f_1457_, 8, v___x_1436_);
lean_closure_set(v___f_1457_, 9, v___x_1429_);
lean_closure_set(v___f_1457_, 10, v_00_u03c3s_1410_);
lean_closure_set(v___f_1457_, 11, v_hyps_1411_);
lean_closure_set(v___f_1457_, 12, v_a_1449_);
lean_closure_set(v___f_1457_, 13, v_target_1412_);
lean_closure_set(v___f_1457_, 14, v_a_1443_);
v___x_1458_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_a_1452_, v_a_1420_, v___f_1457_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1458_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1449_);
lean_dec(v_a_1446_);
lean_dec(v_a_1443_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
v_a_1460_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1451_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1451_);
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
else
{
lean_dec(v_a_1446_);
lean_dec(v_a_1443_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
return v___x_1448_;
}
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_a_1446_);
lean_dec(v_a_1443_);
lean_dec(v_a_1435_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
v___x_1468_ = lean_apply_9(v_kFail_1398_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
return v___x_1468_;
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1443_);
lean_dec(v_a_1435_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_dec_ref(v_kFail_1398_);
v_a_1469_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1445_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1445_);
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
lean_object* v___x_1477_; 
lean_dec(v_a_1442_);
lean_dec(v_a_1435_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
v___x_1477_ = lean_apply_9(v_kFail_1398_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
return v___x_1477_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_a_1435_);
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_dec_ref(v_kFail_1398_);
v_a_1478_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1441_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1441_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1429_, 2);
lean_dec(v_a_1420_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_dec_ref(v_kFail_1398_);
return v___x_1434_;
}
}
}
}
else
{
lean_del_object(v___x_1414_);
lean_dec_ref(v_target_1412_);
lean_dec_ref(v_hyps_1411_);
lean_dec_ref(v_00_u03c3s_1410_);
lean_dec(v_u_1409_);
lean_dec_ref(v_kSuccess_1399_);
lean_dec_ref(v_kFail_1398_);
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___boxed(lean_object* v_goal_1489_, lean_object* v_kFail_1490_, lean_object* v_kSuccess_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_goal_1489_, v_kFail_1490_, v_kSuccess_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(lean_object* v_a_1505_, lean_object* v___f_1506_, lean_object* v___f_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
lean_inc(v_a_1505_);
v___x_1517_ = l_Lean_MVarId_getType(v_a_1505_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_a_1518_, v___y_1513_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1520_);
lean_dec(v_a_1520_);
if (lean_obj_tag(v___x_1521_) == 1)
{
lean_object* v_val_1522_; lean_object* v___x_1523_; 
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_val_1522_, v___f_1506_, v___f_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_a_1505_, v_a_1524_, v___y_1513_);
return v___x_1525_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1505_);
v_a_1526_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1523_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1523_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v___x_1521_);
lean_dec_ref(v___f_1507_);
lean_dec_ref(v___f_1506_);
lean_dec(v_a_1505_);
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1);
v___x_1535_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v___x_1534_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1535_;
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v___f_1507_);
lean_dec_ref(v___f_1506_);
lean_dec(v_a_1505_);
v_a_1536_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1517_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1517_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed(lean_object* v_a_1544_, lean_object* v___f_1545_, lean_object* v___f_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(v_a_1544_, v___f_1545_, v___f_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1560_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_n(v_a_1569_, 2);
lean_dec_ref_known(v___x_1568_, 1);
v___f_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0));
v___f_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1));
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1572_, 0, v_a_1569_);
lean_closure_set(v___f_1572_, 1, v___f_1570_);
lean_closure_set(v___f_1572_, 2, v___f_1571_);
v___x_1573_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_a_1569_, v___f_1572_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
return v___x_1573_;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1568_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1568_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___boxed(lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(lean_object* v_x_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed(lean_object* v_x_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(v_x_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_x_1603_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(lean_object* v_00_u03b1_1614_, lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(v_msg_1615_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_msg_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(v_00_u03b1_1625_, v_msg_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(lean_object* v_mvarId_1636_, lean_object* v_val_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_mvarId_1636_, v_val_1637_, v___y_1643_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___boxed(lean_object* v_mvarId_1648_, lean_object* v_val_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(v_mvarId_1648_, v_val_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(lean_object* v_00_u03b1_1660_, lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v_msg_1661_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(v_00_u03b1_1672_, v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1684_, lean_object* v_name_1685_, uint8_t v_bi_1686_, lean_object* v_type_1687_, lean_object* v_k_1688_, uint8_t v_kind_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_1685_, v_bi_1686_, v_type_1687_, v_k_1688_, v_kind_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_name_1701_, lean_object* v_bi_1702_, lean_object* v_type_1703_, lean_object* v_k_1704_, lean_object* v_kind_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_bi_boxed_1715_; uint8_t v_kind_boxed_1716_; lean_object* v_res_1717_; 
v_bi_boxed_1715_ = lean_unbox(v_bi_1702_);
v_kind_boxed_1716_ = lean_unbox(v_kind_1705_);
v_res_1717_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(v_00_u03b1_1700_, v_name_1701_, v_bi_boxed_1715_, v_type_1703_, v_k_1704_, v_kind_boxed_1716_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(lean_object* v_00_u03b1_1718_, lean_object* v_name_1719_, lean_object* v_type_1720_, lean_object* v_k_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_1719_, v_type_1720_, v_k_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_name_1733_, lean_object* v_type_1734_, lean_object* v_k_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(v_00_u03b1_1732_, v_name_1733_, v_type_1734_, v_k_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5(lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_x_1747_, v_x_1748_, v_x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1751_, lean_object* v_x_1752_, size_t v_x_1753_, size_t v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_1752_, v_x_1753_, v_x_1754_, v_x_1755_, v_x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
size_t v_x_11914__boxed_1764_; size_t v_x_11915__boxed_1765_; lean_object* v_res_1766_; 
v_x_11914__boxed_1764_ = lean_unbox_usize(v_x_1760_);
lean_dec(v_x_1760_);
v_x_11915__boxed_1765_ = lean_unbox_usize(v_x_1761_);
lean_dec(v_x_1761_);
v_res_1766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(v_00_u03b2_1758_, v_x_1759_, v_x_11914__boxed_1764_, v_x_11915__boxed_1765_, v_x_1762_, v_x_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1767_, lean_object* v_n_1768_, lean_object* v_k_1769_, lean_object* v_v_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v_n_1768_, v_k_1769_, v_v_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1772_, size_t v_depth_1773_, lean_object* v_keys_1774_, lean_object* v_vals_1775_, lean_object* v_heq_1776_, lean_object* v_i_1777_, lean_object* v_entries_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_1773_, v_keys_1774_, v_vals_1775_, v_i_1777_, v_entries_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_depth_1781_, lean_object* v_keys_1782_, lean_object* v_vals_1783_, lean_object* v_heq_1784_, lean_object* v_i_1785_, lean_object* v_entries_1786_){
_start:
{
size_t v_depth_boxed_1787_; lean_object* v_res_1788_; 
v_depth_boxed_1787_ = lean_unbox_usize(v_depth_1781_);
lean_dec(v_depth_1781_);
v_res_1788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_1780_, v_depth_boxed_1787_, v_keys_1782_, v_vals_1783_, v_heq_1784_, v_i_1785_, v_entries_1786_);
lean_dec_ref(v_vals_1783_);
lean_dec_ref(v_keys_1782_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_00_u03b2_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_x_1790_, v_x_1791_, v_x_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1(){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1814_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3));
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7));
v___x_1817_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed), 10, 0);
v___x_1818_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1814_, v___x_1815_, v___x_1816_, v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___boxed(lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
return v_res_1820_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
