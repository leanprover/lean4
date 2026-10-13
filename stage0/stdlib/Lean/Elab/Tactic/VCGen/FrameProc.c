// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.FrameProc
// Imports: public import Lean.Elab.Tactic.VCGen.WPApp public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.AlphaShareBuilder public import Lean.Meta.Tactic.Grind.Types import Std.Internal.Order.Basic import Lean.Meta.AppBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Tactic.Util
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_Pred(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_wp(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_decline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_decline_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_commit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_commit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "frameproc: no lattice split applies to"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_excessStates_7_; lean_object* v_k_8_; lean_object* v___x_9_; 
v_excessStates_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_excessStates_7_);
v_k_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_k_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_excessStates_7_, v_k_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_decline_elim___redArg(lean_object* v_t_22_, lean_object* v_decline_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(v_t_22_, v_decline_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_decline_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_decline_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(v_t_26_, v_decline_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_commit_elim___redArg(lean_object* v_t_30_, lean_object* v_commit_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(v_t_30_, v_commit_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_commit_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_commit_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ctorElim___redArg(v_t_34_, v_commit_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = lean_mk_array(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__0);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1, &l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs___closed__1);
return v___x_44_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object* v_a_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
else
{
lean_object* v_key_48_; lean_object* v_tail_49_; uint8_t v___x_50_; 
v_key_48_ = lean_ctor_get(v_x_46_, 0);
v_tail_49_ = lean_ctor_get(v_x_46_, 2);
v___x_50_ = lean_name_eq(v_key_48_, v_a_45_);
if (v___x_50_ == 0)
{
v_x_46_ = v_tail_49_;
goto _start;
}
else
{
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_a_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object* v_a_56_, lean_object* v_b_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_dec(v_b_57_);
lean_dec(v_a_56_);
return v_x_58_;
}
else
{
lean_object* v_key_59_; lean_object* v_value_60_; lean_object* v_tail_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_73_; 
v_key_59_ = lean_ctor_get(v_x_58_, 0);
v_value_60_ = lean_ctor_get(v_x_58_, 1);
v_tail_61_ = lean_ctor_get(v_x_58_, 2);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_73_ == 0)
{
v___x_63_ = v_x_58_;
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_tail_61_);
lean_inc(v_value_60_);
lean_inc(v_key_59_);
lean_dec(v_x_58_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_73_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
uint8_t v___x_65_; 
v___x_65_ = lean_name_eq(v_key_59_, v_a_56_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_66_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_56_, v_b_57_, v_tail_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 2, v___x_66_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_key_59_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_value_60_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v___x_71_; 
lean_dec(v_value_60_);
lean_dec(v_key_59_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v_b_57_);
lean_ctor_set(v___x_63_, 0, v_a_56_);
v___x_71_ = v___x_63_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_56_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_b_57_);
lean_ctor_set(v_reuseFailAlloc_72_, 2, v_tail_61_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
return v_x_74_;
}
else
{
lean_object* v_key_76_; lean_object* v_value_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_104_; 
v_key_76_ = lean_ctor_get(v_x_75_, 0);
v_value_77_ = lean_ctor_get(v_x_75_, 1);
v_tail_78_ = lean_ctor_get(v_x_75_, 2);
v_isSharedCheck_104_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_104_ == 0)
{
v___x_80_ = v_x_75_;
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_value_77_);
lean_inc(v_key_76_);
lean_dec(v_x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_104_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; uint64_t v___y_84_; 
v___x_82_ = lean_array_get_size(v_x_74_);
if (lean_obj_tag(v_key_76_) == 0)
{
uint64_t v___x_102_; 
v___x_102_ = 1723ULL;
v___y_84_ = v___x_102_;
goto v___jp_83_;
}
else
{
uint64_t v_hash_103_; 
v_hash_103_ = lean_ctor_get_uint64(v_key_76_, sizeof(void*)*2);
v___y_84_ = v_hash_103_;
goto v___jp_83_;
}
v___jp_83_:
{
uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v_fold_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_85_ = 32ULL;
v___x_86_ = lean_uint64_shift_right(v___y_84_, v___x_85_);
v_fold_87_ = lean_uint64_xor(v___y_84_, v___x_86_);
v___x_88_ = 16ULL;
v___x_89_ = lean_uint64_shift_right(v_fold_87_, v___x_88_);
v___x_90_ = lean_uint64_xor(v_fold_87_, v___x_89_);
v___x_91_ = lean_uint64_to_usize(v___x_90_);
v___x_92_ = lean_usize_of_nat(v___x_82_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_usize_land(v___x_91_, v___x_94_);
v___x_96_ = lean_array_uget_borrowed(v_x_74_, v___x_95_);
lean_inc(v___x_96_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 2, v___x_96_);
v___x_98_ = v___x_80_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_76_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_77_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___x_96_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_array_uset(v_x_74_, v___x_95_, v___x_98_);
v_x_74_ = v___x_99_;
v_x_75_ = v_tail_78_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_105_, lean_object* v_source_106_, lean_object* v_target_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_array_get_size(v_source_106_);
v___x_109_ = lean_nat_dec_lt(v_i_105_, v___x_108_);
if (v___x_109_ == 0)
{
lean_dec_ref(v_source_106_);
lean_dec(v_i_105_);
return v_target_107_;
}
else
{
lean_object* v_es_110_; lean_object* v___x_111_; lean_object* v_source_112_; lean_object* v_target_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_es_110_ = lean_array_fget(v_source_106_, v_i_105_);
v___x_111_ = lean_box(0);
v_source_112_ = lean_array_fset(v_source_106_, v_i_105_, v___x_111_);
v_target_113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_107_, v_es_110_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v_i_105_, v___x_114_);
lean_dec(v_i_105_);
v_i_105_ = v___x_115_;
v_source_106_ = v_source_112_;
v_target_107_ = v_target_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object* v_data_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_nbuckets_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_118_ = lean_array_get_size(v_data_117_);
v___x_119_ = lean_unsigned_to_nat(2u);
v_nbuckets_120_ = lean_nat_mul(v___x_118_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_box(0);
v___x_123_ = lean_mk_array(v_nbuckets_120_, v___x_122_);
v___x_124_ = lean_array_propagate_mark(v_data_117_, v___x_123_);
v___x_125_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v___x_121_, v_data_117_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(lean_object* v_m_126_, lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
lean_object* v_size_129_; lean_object* v_buckets_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_176_; 
v_size_129_ = lean_ctor_get(v_m_126_, 0);
v_buckets_130_ = lean_ctor_get(v_m_126_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_m_126_);
if (v_isSharedCheck_176_ == 0)
{
v___x_132_ = v_m_126_;
v_isShared_133_ = v_isSharedCheck_176_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_buckets_130_);
lean_inc(v_size_129_);
lean_dec(v_m_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_176_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; uint64_t v___y_136_; 
v___x_134_ = lean_array_get_size(v_buckets_130_);
if (lean_obj_tag(v_a_127_) == 0)
{
uint64_t v___x_174_; 
v___x_174_ = 1723ULL;
v___y_136_ = v___x_174_;
goto v___jp_135_;
}
else
{
uint64_t v_hash_175_; 
v_hash_175_ = lean_ctor_get_uint64(v_a_127_, sizeof(void*)*2);
v___y_136_ = v_hash_175_;
goto v___jp_135_;
}
v___jp_135_:
{
uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v_fold_139_; uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; lean_object* v_bkt_148_; uint8_t v___x_149_; 
v___x_137_ = 32ULL;
v___x_138_ = lean_uint64_shift_right(v___y_136_, v___x_137_);
v_fold_139_ = lean_uint64_xor(v___y_136_, v___x_138_);
v___x_140_ = 16ULL;
v___x_141_ = lean_uint64_shift_right(v_fold_139_, v___x_140_);
v___x_142_ = lean_uint64_xor(v_fold_139_, v___x_141_);
v___x_143_ = lean_uint64_to_usize(v___x_142_);
v___x_144_ = lean_usize_of_nat(v___x_134_);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_sub(v___x_144_, v___x_145_);
v___x_147_ = lean_usize_land(v___x_143_, v___x_146_);
v_bkt_148_ = lean_array_uget_borrowed(v_buckets_130_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_127_, v_bkt_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v_size_x27_151_; lean_object* v___x_152_; lean_object* v_buckets_x27_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v_size_x27_151_ = lean_nat_add(v_size_129_, v___x_150_);
lean_dec(v_size_129_);
lean_inc(v_bkt_148_);
v___x_152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_152_, 0, v_a_127_);
lean_ctor_set(v___x_152_, 1, v_b_128_);
lean_ctor_set(v___x_152_, 2, v_bkt_148_);
v_buckets_x27_153_ = lean_array_uset(v_buckets_130_, v___x_147_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = lean_nat_mul(v_size_x27_151_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(3u);
v___x_157_ = lean_nat_div(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_array_get_size(v_buckets_x27_153_);
v___x_159_ = lean_nat_dec_le(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
if (v___x_159_ == 0)
{
lean_object* v_val_160_; lean_object* v___x_162_; 
v_val_160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_buckets_x27_153_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_val_160_);
lean_ctor_set(v___x_132_, 0, v_size_x27_151_);
v___x_162_ = v___x_132_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_151_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_val_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v___x_165_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_buckets_x27_153_);
lean_ctor_set(v___x_132_, 0, v_size_x27_151_);
v___x_165_ = v___x_132_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_x27_151_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_buckets_x27_153_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v___x_167_; lean_object* v_buckets_x27_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
lean_inc(v_bkt_148_);
v___x_167_ = lean_box(0);
v_buckets_x27_168_ = lean_array_uset(v_buckets_130_, v___x_147_, v___x_167_);
v___x_169_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_127_, v_b_128_, v_bkt_148_);
v___x_170_ = lean_array_uset(v_buckets_x27_168_, v___x_147_, v___x_169_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_170_);
v___x_172_ = v___x_132_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_size_129_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(lean_object* v_s_177_, lean_object* v_fp_178_){
_start:
{
lean_object* v_prog_179_; lean_object* v___x_180_; 
v_prog_179_ = lean_ctor_get(v_fp_178_, 0);
lean_inc(v_prog_179_);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(v_s_177_, v_prog_179_, v_fp_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0(lean_object* v_00_u03b2_181_, lean_object* v_m_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(v_m_182_, v_a_183_, v_b_184_);
return v___x_185_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_a_187_, lean_object* v_x_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_190_, lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(v_00_u03b2_190_, v_a_191_, v_x_192_);
lean_dec(v_x_192_);
lean_dec(v_a_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object* v_00_u03b2_195_, lean_object* v_data_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_data_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_b_200_, lean_object* v_x_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_199_, v_b_200_, v_x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_203_, lean_object* v_i_204_, lean_object* v_source_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v_i_204_, v_source_205_, v_target_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_209_, v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(lean_object* v_f_212_, lean_object* v_a_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___y_222_; lean_object* v___x_225_; uint8_t v_debug_226_; 
v___x_225_ = lean_st_ref_get(v___y_215_);
v_debug_226_ = lean_ctor_get_uint8(v___x_225_, sizeof(void*)*12);
lean_dec(v___x_225_);
if (v_debug_226_ == 0)
{
v___y_222_ = v___y_215_;
goto v___jp_221_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_212_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec_ref_known(v___x_227_, 1);
v___x_228_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_dec_ref_known(v___x_228_, 1);
v___y_222_ = v___y_215_;
goto v___jp_221_;
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v_a_213_);
lean_dec_ref(v_f_212_);
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
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
lean_dec_ref(v_a_213_);
lean_dec_ref(v_f_212_);
v_a_237_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_227_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_227_);
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
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l_Lean_Expr_app___override(v_f_212_, v_a_213_);
v___x_224_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_223_, v___y_222_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_245_, lean_object* v_a_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_245_, v_a_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(lean_object* v_args_255_, lean_object* v_endIdx_256_, lean_object* v_b_257_, lean_object* v_i_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_le(v_endIdx_256_, v_i_258_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_instInhabitedExpr;
v___x_271_ = lean_array_get_borrowed(v___x_270_, v_args_255_, v_i_258_);
lean_inc(v___x_271_);
v___x_272_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_b_257_, v___x_271_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_add(v_i_258_, v___x_274_);
lean_dec(v_i_258_);
v_b_257_ = v_a_273_;
v_i_258_ = v___x_275_;
goto _start;
}
else
{
lean_dec(v_i_258_);
return v___x_272_;
}
}
else
{
lean_object* v___x_277_; 
lean_dec(v_i_258_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v_b_257_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2___boxed(lean_object* v_args_278_, lean_object* v_endIdx_279_, lean_object* v_b_280_, lean_object* v_i_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(v_args_278_, v_endIdx_279_, v_b_280_, v_i_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec(v_endIdx_279_);
lean_dec_ref(v_args_278_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(lean_object* v_f_293_, lean_object* v_args_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_array_get_size(v_args_294_);
v___x_307_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(v_args_294_, v___x_306_, v_f_293_, v___x_305_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1___boxed(lean_object* v_f_308_, lean_object* v_args_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_f_308_, v_args_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v_args_309_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_350_; 
v_ks_325_ = lean_ctor_get(v_x_321_, 0);
v_vs_326_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_350_ == 0)
{
v___x_328_ = v_x_321_;
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_vs_326_);
lean_inc(v_ks_325_);
lean_dec(v_x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_350_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = lean_array_get_size(v_ks_325_);
v___x_331_ = lean_nat_dec_lt(v_x_322_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_x_322_);
v___x_332_ = lean_array_push(v_ks_325_, v_x_323_);
v___x_333_ = lean_array_push(v_vs_326_, v_x_324_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
lean_ctor_set(v___x_328_, 0, v___x_332_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v_k_x27_337_; uint8_t v___x_338_; 
v_k_x27_337_ = lean_array_fget_borrowed(v_ks_325_, v_x_322_);
v___x_338_ = l_Lean_instBEqMVarId_beq(v_x_323_, v_k_x27_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_340_; 
if (v_isShared_329_ == 0)
{
v___x_340_ = v___x_328_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_326_);
v___x_340_ = v_reuseFailAlloc_344_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_x_322_, v___x_341_);
lean_dec(v_x_322_);
v_x_321_ = v___x_340_;
v_x_322_ = v___x_342_;
goto _start;
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_array_fset(v_ks_325_, v_x_322_, v_x_323_);
v___x_346_ = lean_array_fset(v_vs_326_, v_x_322_, v_x_324_);
lean_dec(v_x_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_346_);
lean_ctor_set(v___x_328_, 0, v___x_345_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_n_351_, lean_object* v_k_352_, lean_object* v_v_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_n_351_, v___x_354_, v_k_352_, v_v_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(lean_object* v_x_357_, size_t v_x_358_, size_t v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v_es_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v_j_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_es_362_ = lean_ctor_get(v_x_357_, 0);
v___x_363_ = ((size_t)31ULL);
v___x_364_ = lean_usize_land(v_x_358_, v___x_363_);
v_j_365_ = lean_usize_to_nat(v___x_364_);
v___x_366_ = lean_array_get_size(v_es_362_);
v___x_367_ = lean_nat_dec_lt(v_j_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_dec(v_j_365_);
lean_dec(v_x_361_);
lean_dec(v_x_360_);
return v_x_357_;
}
else
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_406_; 
lean_inc_ref(v_es_362_);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_x_357_, 0);
lean_dec(v_unused_407_);
v___x_369_ = v_x_357_;
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_406_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_v_371_; lean_object* v___x_372_; lean_object* v_xs_x27_373_; lean_object* v___y_375_; 
v_v_371_ = lean_array_fget(v_es_362_, v_j_365_);
v___x_372_ = lean_box(0);
v_xs_x27_373_ = lean_array_fset(v_es_362_, v_j_365_, v___x_372_);
switch(lean_obj_tag(v_v_371_))
{
case 0:
{
lean_object* v_key_380_; lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_391_; 
v_key_380_ = lean_ctor_get(v_v_371_, 0);
v_val_381_ = lean_ctor_get(v_v_371_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_v_371_);
if (v_isSharedCheck_391_ == 0)
{
v___x_383_ = v_v_371_;
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_inc(v_key_380_);
lean_dec(v_v_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_instBEqMVarId_beq(v_x_360_, v_key_380_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_del_object(v___x_383_);
v___x_386_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_380_, v_val_381_, v_x_360_, v_x_361_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
v___y_375_ = v___x_387_;
goto v___jp_374_;
}
else
{
lean_object* v___x_389_; 
lean_dec(v_val_381_);
lean_dec(v_key_380_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_x_361_);
lean_ctor_set(v___x_383_, 0, v_x_360_);
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_x_360_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_x_361_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_375_ = v___x_389_;
goto v___jp_374_;
}
}
}
}
case 1:
{
lean_object* v_node_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_node_392_ = lean_ctor_get(v_v_371_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_v_371_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v_v_371_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_node_392_);
lean_dec(v_v_371_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_usize_shift_right(v_x_358_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_x_359_, v___x_398_);
v___x_400_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_node_392_, v___x_397_, v___x_399_, v_x_360_, v_x_361_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v___y_375_ = v___x_402_;
goto v___jp_374_;
}
}
}
default: 
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_x_360_);
lean_ctor_set(v___x_405_, 1, v_x_361_);
v___y_375_ = v___x_405_;
goto v___jp_374_;
}
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_array_fset(v_xs_x27_373_, v_j_365_, v___y_375_);
lean_dec(v_j_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_376_);
v___x_378_ = v___x_369_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_ks_408_; lean_object* v_vs_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_427_; 
v_ks_408_ = lean_ctor_get(v_x_357_, 0);
v_vs_409_ = lean_ctor_get(v_x_357_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_357_);
if (v_isSharedCheck_427_ == 0)
{
v___x_411_ = v_x_357_;
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_vs_409_);
lean_inc(v_ks_408_);
lean_dec(v_x_357_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_ks_408_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_vs_409_);
v___x_414_ = v_reuseFailAlloc_426_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v_newNode_415_; size_t v___x_416_; uint8_t v___x_417_; 
v_newNode_415_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(v___x_414_, v_x_360_, v_x_361_);
v___x_416_ = ((size_t)7ULL);
v___x_417_ = lean_usize_dec_le(v___x_416_, v_x_359_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_415_);
v___x_419_ = lean_unsigned_to_nat(4u);
v___x_420_ = lean_nat_dec_lt(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
if (v___x_420_ == 0)
{
lean_object* v_ks_421_; lean_object* v_vs_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_ks_421_ = lean_ctor_get(v_newNode_415_, 0);
lean_inc_ref(v_ks_421_);
v_vs_422_ = lean_ctor_get(v_newNode_415_, 1);
lean_inc_ref(v_vs_422_);
lean_dec_ref(v_newNode_415_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_x_359_, v_ks_421_, v_vs_422_, v___x_423_, v___x_424_);
lean_dec_ref(v_vs_422_);
lean_dec_ref(v_ks_421_);
return v___x_425_;
}
else
{
return v_newNode_415_;
}
}
else
{
return v_newNode_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(size_t v_depth_428_, lean_object* v_keys_429_, lean_object* v_vals_430_, lean_object* v_i_431_, lean_object* v_entries_432_){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_array_get_size(v_keys_429_);
v___x_434_ = lean_nat_dec_lt(v_i_431_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v_i_431_);
return v_entries_432_;
}
else
{
lean_object* v_k_435_; lean_object* v_v_436_; uint64_t v___x_437_; size_t v_h_438_; size_t v___x_439_; lean_object* v___x_440_; size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v_h_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_k_435_ = lean_array_fget_borrowed(v_keys_429_, v_i_431_);
v_v_436_ = lean_array_fget_borrowed(v_vals_430_, v_i_431_);
v___x_437_ = l_Lean_instHashableMVarId_hash(v_k_435_);
v_h_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_sub(v_depth_428_, v___x_441_);
v___x_443_ = lean_usize_mul(v___x_439_, v___x_442_);
v_h_444_ = lean_usize_shift_right(v_h_438_, v___x_443_);
v___x_445_ = lean_nat_add(v_i_431_, v___x_440_);
lean_dec(v_i_431_);
lean_inc(v_v_436_);
lean_inc(v_k_435_);
v___x_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_entries_432_, v_h_444_, v_depth_428_, v_k_435_, v_v_436_);
v_i_431_ = v___x_445_;
v_entries_432_ = v___x_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_depth_448_, lean_object* v_keys_449_, lean_object* v_vals_450_, lean_object* v_i_451_, lean_object* v_entries_452_){
_start:
{
size_t v_depth_boxed_453_; lean_object* v_res_454_; 
v_depth_boxed_453_ = lean_unbox_usize(v_depth_448_);
lean_dec(v_depth_448_);
v_res_454_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_boxed_453_, v_keys_449_, v_vals_450_, v_i_451_, v_entries_452_);
lean_dec_ref(v_vals_450_);
lean_dec_ref(v_keys_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
size_t v_x_33099__boxed_460_; size_t v_x_33100__boxed_461_; lean_object* v_res_462_; 
v_x_33099__boxed_460_ = lean_unbox_usize(v_x_456_);
lean_dec(v_x_456_);
v_x_33100__boxed_461_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_res_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_455_, v_x_33099__boxed_460_, v_x_33100__boxed_461_, v_x_458_, v_x_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
uint64_t v___x_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_466_ = l_Lean_instHashableMVarId_hash(v_x_464_);
v___x_467_ = lean_uint64_to_usize(v___x_466_);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_463_, v___x_467_, v___x_468_, v_x_464_, v_x_465_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(lean_object* v_mvarId_470_, lean_object* v_val_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; lean_object* v_mctx_475_; lean_object* v_cache_476_; lean_object* v_zetaDeltaFVarIds_477_; lean_object* v_postponed_478_; lean_object* v_diag_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_509_; 
v___x_474_ = lean_st_ref_take(v___y_472_);
v_mctx_475_ = lean_ctor_get(v___x_474_, 0);
v_cache_476_ = lean_ctor_get(v___x_474_, 1);
v_zetaDeltaFVarIds_477_ = lean_ctor_get(v___x_474_, 2);
v_postponed_478_ = lean_ctor_get(v___x_474_, 3);
v_diag_479_ = lean_ctor_get(v___x_474_, 4);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_509_ == 0)
{
v___x_481_ = v___x_474_;
v_isShared_482_ = v_isSharedCheck_509_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_diag_479_);
lean_inc(v_postponed_478_);
lean_inc(v_zetaDeltaFVarIds_477_);
lean_inc(v_cache_476_);
lean_inc(v_mctx_475_);
lean_dec(v___x_474_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_509_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_depth_483_; lean_object* v_levelAssignDepth_484_; lean_object* v_lmvarCounter_485_; lean_object* v_mvarCounter_486_; lean_object* v_lDecls_487_; lean_object* v_decls_488_; lean_object* v_userNames_489_; lean_object* v_lAssignment_490_; lean_object* v_eAssignment_491_; lean_object* v_dAssignment_492_; lean_object* v_instanceTypedMVars_493_; lean_object* v_synthNormMemo_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_508_; 
v_depth_483_ = lean_ctor_get(v_mctx_475_, 0);
v_levelAssignDepth_484_ = lean_ctor_get(v_mctx_475_, 1);
v_lmvarCounter_485_ = lean_ctor_get(v_mctx_475_, 2);
v_mvarCounter_486_ = lean_ctor_get(v_mctx_475_, 3);
v_lDecls_487_ = lean_ctor_get(v_mctx_475_, 4);
v_decls_488_ = lean_ctor_get(v_mctx_475_, 5);
v_userNames_489_ = lean_ctor_get(v_mctx_475_, 6);
v_lAssignment_490_ = lean_ctor_get(v_mctx_475_, 7);
v_eAssignment_491_ = lean_ctor_get(v_mctx_475_, 8);
v_dAssignment_492_ = lean_ctor_get(v_mctx_475_, 9);
v_instanceTypedMVars_493_ = lean_ctor_get(v_mctx_475_, 10);
v_synthNormMemo_494_ = lean_ctor_get(v_mctx_475_, 11);
v_isSharedCheck_508_ = !lean_is_exclusive(v_mctx_475_);
if (v_isSharedCheck_508_ == 0)
{
v___x_496_ = v_mctx_475_;
v_isShared_497_ = v_isSharedCheck_508_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_synthNormMemo_494_);
lean_inc(v_instanceTypedMVars_493_);
lean_inc(v_dAssignment_492_);
lean_inc(v_eAssignment_491_);
lean_inc(v_lAssignment_490_);
lean_inc(v_userNames_489_);
lean_inc(v_decls_488_);
lean_inc(v_lDecls_487_);
lean_inc(v_mvarCounter_486_);
lean_inc(v_lmvarCounter_485_);
lean_inc(v_levelAssignDepth_484_);
lean_inc(v_depth_483_);
lean_dec(v_mctx_475_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_508_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = lean_box(0);
v___x_499_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_eAssignment_491_, v_mvarId_470_, v_val_471_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 8, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_depth_483_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_levelAssignDepth_484_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_lmvarCounter_485_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_mvarCounter_486_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_lDecls_487_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_decls_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_userNames_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v_lAssignment_490_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_507_, 9, v_dAssignment_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 10, v_instanceTypedMVars_493_);
lean_ctor_set(v_reuseFailAlloc_507_, 11, v_synthNormMemo_494_);
v___x_501_ = v_reuseFailAlloc_507_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_501_);
v___x_503_ = v___x_481_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_cache_476_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_zetaDeltaFVarIds_477_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_postponed_478_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_diag_479_);
v___x_503_ = v_reuseFailAlloc_506_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_st_ref_put(v___y_472_, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_498_);
return v___x_505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg___boxed(lean_object* v_mvarId_510_, lean_object* v_val_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_510_, v_val_511_, v___y_512_);
lean_dec(v___y_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(lean_object* v_msgData_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v_env_522_; uint8_t v___x_523_; lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v_toCold_526_; lean_object* v_mctx_527_; lean_object* v_lctx_528_; lean_object* v_options_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_521_ = lean_st_ref_get(v___y_519_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_env_522_);
lean_dec(v___x_521_);
v___x_523_ = 0;
v_env_524_ = l_Lean_Environment_setRecordingDeps(v_env_522_, v___x_523_);
v___x_525_ = lean_st_ref_get(v___y_517_);
v_toCold_526_ = lean_ctor_get(v___y_518_, 0);
v_mctx_527_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_mctx_527_);
lean_dec(v___x_525_);
v_lctx_528_ = lean_ctor_get(v___y_516_, 2);
v_options_529_ = lean_ctor_get(v_toCold_526_, 2);
lean_inc_ref(v_options_529_);
lean_inc_ref(v_lctx_528_);
v___x_530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_530_, 0, v_env_524_);
lean_ctor_set(v___x_530_, 1, v_mctx_527_);
lean_ctor_set(v___x_530_, 2, v_lctx_528_);
lean_ctor_set(v___x_530_, 3, v_options_529_);
v___x_531_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_msgData_515_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5___boxed(lean_object* v_msgData_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msgData_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_ref_546_; lean_object* v___x_547_; lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
v_ref_546_ = lean_ctor_get(v___y_543_, 2);
v___x_547_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_556_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_inc(v_ref_546_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_ref_546_);
lean_ctor_set(v___x_552_, 1, v_a_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 1);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg___boxed(lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(lean_object* v_goal_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref(v_goal_564_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_x_566_);
return v___x_577_;
}
else
{
lean_object* v_head_578_; lean_object* v_tail_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
v_head_578_ = lean_ctor_get(v_x_565_, 0);
v_tail_579_ = lean_ctor_get(v_x_565_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_602_ == 0)
{
v___x_581_ = v_x_565_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_tail_579_);
lean_inc(v_head_578_);
lean_dec(v_x_565_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
lean_inc(v_head_578_);
v___x_583_ = l_Lean_MVarId_getType(v_head_578_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = l_Lean_Expr_appArg_x21(v_a_584_);
lean_dec(v_a_584_);
v___x_586_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_x_566_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_head_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_x_566_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v_x_565_ = v_tail_579_;
v_x_566_ = v___x_588_;
goto _start;
}
}
else
{
lean_object* v_specProof_591_; lean_object* v___x_592_; 
lean_dec_ref_known(v___x_586_, 1);
lean_del_object(v___x_581_);
v_specProof_591_ = lean_ctor_get(v_goal_564_, 5);
lean_inc_ref(v_specProof_591_);
v___x_592_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_head_578_, v_specProof_591_, v___y_573_);
lean_dec_ref(v___x_592_);
v_x_565_ = v_tail_579_;
goto _start;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_del_object(v___x_581_);
lean_dec(v_tail_579_);
lean_dec(v_head_578_);
lean_dec(v_x_566_);
lean_dec_ref(v_goal_564_);
v_a_594_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_583_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_583_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2___boxed(lean_object* v_goal_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_603_, v_x_604_, v_x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(lean_object* v_frame_620_, lean_object* v_pre_621_, lean_object* v_mkOpApp_622_, lean_object* v_excessArgs_623_, lean_object* v_le_624_, lean_object* v_goal_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Sym_shareCommon(v_frame_620_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_frame_638_; lean_object* v_footprint_639_; lean_object* v_framedApp_640_; lean_object* v_splitLatticeOp_x3f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_n(v_a_637_, 2);
lean_dec_ref_known(v___x_636_, 1);
v_frame_638_ = lean_ctor_get(v_goal_625_, 0);
v_footprint_639_ = lean_ctor_get(v_goal_625_, 1);
v_framedApp_640_ = lean_ctor_get(v_goal_625_, 2);
v_splitLatticeOp_x3f_641_ = lean_ctor_get(v_goal_625_, 6);
lean_inc(v_frame_638_);
v___x_642_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_frame_638_, v_a_637_, v___y_632_);
lean_dec_ref(v___x_642_);
lean_inc_ref(v_pre_621_);
lean_inc(v_footprint_639_);
v___x_643_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_footprint_639_, v_pre_621_, v___y_632_);
lean_dec_ref(v___x_643_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
lean_inc_ref(v___y_631_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
v___x_644_ = lean_apply_7(v_mkOpApp_622_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = l_Lean_Elab_Tactic_VCGen_WPApp_wp(v_framedApp_640_);
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
lean_inc_ref(v___x_648_);
v___x_649_ = lean_array_push(v___x_648_, v_a_637_);
v___x_650_ = lean_array_push(v___x_649_, v___x_646_);
v___x_651_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_645_, v___x_650_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec_ref(v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_652_, v_excessArgs_623_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_array_push(v___x_648_, v_pre_621_);
v___x_656_ = lean_array_push(v___x_655_, v_a_654_);
v___x_657_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_le_624_, v___x_656_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec_ref(v___x_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_658_, v___x_659_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_710_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_710_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_710_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_710_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_a_666_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = l_Lean_Expr_mvarId_x21(v_a_661_);
lean_inc_ref(v_splitLatticeOp_x3f_641_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
lean_inc_ref(v___y_631_);
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc(v___y_626_);
lean_inc(v___x_671_);
v___x_672_ = lean_apply_11(v_splitLatticeOp_x3f_641_, v___x_671_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, lean_box(0));
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_671_);
v_val_674_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_a_673_, 1);
v___x_675_ = lean_box(0);
v___x_676_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_625_, v_val_674_, v___x_675_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_List_reverse___redArg(v_a_677_);
v_a_666_ = v___x_678_;
goto v___jp_665_;
}
else
{
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_676_, 1);
v_a_666_ = v_a_679_;
goto v___jp_665_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_del_object(v___x_663_);
lean_dec(v_a_661_);
v_a_680_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_676_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_676_);
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
}
else
{
lean_object* v___x_688_; 
lean_dec(v_a_673_);
lean_del_object(v___x_663_);
lean_dec(v_a_661_);
lean_dec_ref(v_goal_625_);
v___x_688_ = l_Lean_MVarId_getType(v___x_671_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1);
v___x_691_ = l_Lean_indentExpr(v_a_689_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v___x_692_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
return v___x_693_;
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_688_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_688_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v___x_671_);
lean_del_object(v___x_663_);
lean_dec(v_a_661_);
lean_dec_ref(v_goal_625_);
v_a_702_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_672_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_672_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_a_661_);
lean_ctor_set(v___x_667_, 1, v_a_666_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_667_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_goal_625_);
v_a_711_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_660_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_660_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v_goal_625_);
v_a_719_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_657_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_657_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_goal_625_);
lean_dec_ref(v_le_624_);
lean_dec_ref(v_pre_621_);
v_a_727_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_653_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_653_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_goal_625_);
lean_dec_ref(v_le_624_);
lean_dec_ref(v_pre_621_);
v_a_735_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_651_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_651_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_637_);
lean_dec_ref(v_goal_625_);
lean_dec_ref(v_le_624_);
lean_dec_ref(v_pre_621_);
v_a_743_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_644_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_644_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_goal_625_);
lean_dec_ref(v_le_624_);
lean_dec_ref(v_mkOpApp_622_);
lean_dec_ref(v_pre_621_);
v_a_751_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_636_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_636_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed(lean_object* v_frame_759_, lean_object* v_pre_760_, lean_object* v_mkOpApp_761_, lean_object* v_excessArgs_762_, lean_object* v_le_763_, lean_object* v_goal_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(v_frame_759_, v_pre_760_, v_mkOpApp_761_, v_excessArgs_762_, v_le_763_, v_goal_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v_excessArgs_762_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(lean_object* v_i_776_, lean_object* v_frame_777_){
_start:
{
lean_object* v_unframedApp_778_; lean_object* v_pre_779_; lean_object* v_le_780_; lean_object* v_mkOpApp_781_; lean_object* v_excessArgs_782_; lean_object* v___f_783_; lean_object* v___x_784_; 
v_unframedApp_778_ = lean_ctor_get(v_i_776_, 2);
lean_inc_ref(v_unframedApp_778_);
v_pre_779_ = lean_ctor_get(v_i_776_, 0);
lean_inc_ref(v_pre_779_);
v_le_780_ = lean_ctor_get(v_i_776_, 1);
lean_inc_ref(v_le_780_);
v_mkOpApp_781_ = lean_ctor_get(v_i_776_, 5);
lean_inc_ref(v_mkOpApp_781_);
lean_dec_ref(v_i_776_);
v_excessArgs_782_ = lean_ctor_get(v_unframedApp_778_, 3);
lean_inc_ref_n(v_excessArgs_782_, 2);
lean_dec_ref(v_unframedApp_778_);
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed), 16, 5);
lean_closure_set(v___f_783_, 0, v_frame_777_);
lean_closure_set(v___f_783_, 1, v_pre_779_);
lean_closure_set(v___f_783_, 2, v_mkOpApp_781_);
lean_closure_set(v___f_783_, 3, v_excessArgs_782_);
lean_closure_set(v___f_783_, 4, v_le_780_);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_excessArgs_782_);
lean_ctor_set(v___x_784_, 1, v___f_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(lean_object* v_mvarId_785_, lean_object* v_val_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_785_, v_val_786_, v___y_793_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___boxed(lean_object* v_mvarId_798_, lean_object* v_val_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(v_mvarId_798_, v_val_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(lean_object* v_00_u03b1_811_, lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_812_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___boxed(lean_object* v_00_u03b1_824_, lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(v_00_u03b1_824_, v_msg_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0(lean_object* v_00_u03b2_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_x_838_, v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(lean_object* v_f_842_, lean_object* v_a_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_842_, v_a_843_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___boxed(lean_object* v_f_855_, lean_object* v_a_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(v_f_855_, v_a_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, size_t v_x_870_, size_t v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_869_, v_x_870_, v_x_871_, v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
size_t v_x_33849__boxed_881_; size_t v_x_33850__boxed_882_; lean_object* v_res_883_; 
v_x_33849__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_x_33850__boxed_882_ = lean_unbox_usize(v_x_878_);
lean_dec(v_x_878_);
v_res_883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(v_00_u03b2_875_, v_x_876_, v_x_33849__boxed_881_, v_x_33850__boxed_882_, v_x_879_, v_x_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_884_, lean_object* v_n_885_, lean_object* v_k_886_, lean_object* v_v_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(v_n_885_, v_k_886_, v_v_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_889_, size_t v_depth_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_heq_893_, lean_object* v_i_894_, lean_object* v_entries_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_890_, v_keys_891_, v_vals_892_, v_i_894_, v_entries_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b2_897_, lean_object* v_depth_898_, lean_object* v_keys_899_, lean_object* v_vals_900_, lean_object* v_heq_901_, lean_object* v_i_902_, lean_object* v_entries_903_){
_start:
{
size_t v_depth_boxed_904_; lean_object* v_res_905_; 
v_depth_boxed_904_ = lean_unbox_usize(v_depth_898_);
lean_dec(v_depth_898_);
v_res_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(v_00_u03b2_897_, v_depth_boxed_904_, v_keys_899_, v_vals_900_, v_heq_901_, v_i_902_, v_entries_903_);
lean_dec_ref(v_vals_900_);
lean_dec_ref(v_keys_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_x_907_, v_x_908_, v_x_909_, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(lean_object* v_i_912_){
_start:
{
lean_object* v_providedFrame_x3f_914_; 
v_providedFrame_x3f_914_ = lean_ctor_get(v_i_912_, 3);
lean_inc(v_providedFrame_x3f_914_);
if (lean_obj_tag(v_providedFrame_x3f_914_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_val_915_ = lean_ctor_get(v_providedFrame_x3f_914_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_providedFrame_x3f_914_);
if (v_isSharedCheck_923_ == 0)
{
v___x_917_ = v_providedFrame_x3f_914_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_val_915_);
lean_dec(v_providedFrame_x3f_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(v_i_912_, v_val_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_providedFrame_x3f_914_);
lean_dec_ref(v_i_912_);
v___x_924_ = lean_box(0);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg___boxed(lean_object* v_i_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(lean_object* v_i_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_929_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed(lean_object* v_i_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(v_i_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(lean_object* v_info_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_967_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_960_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_unsigned_to_nat(2u);
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_972_ = lean_array_push(v___x_971_, v___x_968_);
v___x_973_ = lean_array_push(v___x_972_, v___x_969_);
v___x_974_ = l_Lean_Meta_mkAppOptM(v___x_966_, v___x_973_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___boxed(lean_object* v_info_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(v_info_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_info_975_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(lean_object* v_info_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_982_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0___boxed(lean_object* v_info_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(v_info_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_info_990_);
return v_res_996_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2(void){
_start:
{
lean_object* v___x_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed), 11, 0);
v___f_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1));
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
lean_ctor_set(v___x_1003_, 2, v___x_1001_);
lean_ctor_set(v___x_1003_, 3, v___f_1000_);
lean_ctor_set(v___x_1003_, 4, v___x_999_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc(void){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2, &l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2);
return v___x_1004_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs);
l_Lean_Elab_Tactic_VCGen_meetFrameProc = _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_meetFrameProc);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_WPApp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
}
#ifdef __cplusplus
}
#endif
