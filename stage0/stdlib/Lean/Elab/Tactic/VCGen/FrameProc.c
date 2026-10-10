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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object* v_a_45_, lean_object* v_x_46_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_45_ = stack[0].m_obj;
lean_object* v_x_46_ = stack[1].m_obj;
uint8_t v_res_52_;
v_res_52_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_45_, v_x_46_);
stack->m_num = v_res_52_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_53_, v_x_54_);
lean_dec(v_x_54_);
lean_dec(v_a_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object* v_a_57_, lean_object* v_b_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_dec(v_b_58_);
lean_dec(v_a_57_);
return v_x_59_;
}
else
{
lean_object* v_key_60_; lean_object* v_value_61_; lean_object* v_tail_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_74_; 
v_key_60_ = lean_ctor_get(v_x_59_, 0);
v_value_61_ = lean_ctor_get(v_x_59_, 1);
v_tail_62_ = lean_ctor_get(v_x_59_, 2);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_74_ == 0)
{
v___x_64_ = v_x_59_;
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_tail_62_);
lean_inc(v_value_61_);
lean_inc(v_key_60_);
lean_dec(v_x_59_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_74_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
uint8_t v___x_66_; 
v___x_66_ = lean_name_eq(v_key_60_, v_a_57_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_57_, v_b_58_, v_tail_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 2, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_key_60_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_value_61_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
else
{
lean_object* v___x_72_; 
lean_dec(v_value_61_);
lean_dec(v_key_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v_b_58_);
lean_ctor_set(v___x_64_, 0, v_a_57_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_57_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_b_58_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_tail_62_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
return v_x_75_;
}
else
{
lean_object* v_key_77_; lean_object* v_value_78_; lean_object* v_tail_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_105_; 
v_key_77_ = lean_ctor_get(v_x_76_, 0);
v_value_78_ = lean_ctor_get(v_x_76_, 1);
v_tail_79_ = lean_ctor_get(v_x_76_, 2);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_105_ == 0)
{
v___x_81_ = v_x_76_;
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_tail_79_);
lean_inc(v_value_78_);
lean_inc(v_key_77_);
lean_dec(v_x_76_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_105_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; uint64_t v___y_85_; 
v___x_83_ = lean_array_get_size(v_x_75_);
if (lean_obj_tag(v_key_77_) == 0)
{
uint64_t v___x_103_; 
v___x_103_ = 1723ULL;
v___y_85_ = v___x_103_;
goto v___jp_84_;
}
else
{
uint64_t v_hash_104_; 
v_hash_104_ = lean_ctor_get_uint64(v_key_77_, sizeof(void*)*2);
v___y_85_ = v_hash_104_;
goto v___jp_84_;
}
v___jp_84_:
{
uint64_t v___x_86_; uint64_t v___x_87_; uint64_t v_fold_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_86_ = 32ULL;
v___x_87_ = lean_uint64_shift_right(v___y_85_, v___x_86_);
v_fold_88_ = lean_uint64_xor(v___y_85_, v___x_87_);
v___x_89_ = 16ULL;
v___x_90_ = lean_uint64_shift_right(v_fold_88_, v___x_89_);
v___x_91_ = lean_uint64_xor(v_fold_88_, v___x_90_);
v___x_92_ = lean_uint64_to_usize(v___x_91_);
v___x_93_ = lean_usize_of_nat(v___x_83_);
v___x_94_ = ((size_t)1ULL);
v___x_95_ = lean_usize_sub(v___x_93_, v___x_94_);
v___x_96_ = lean_usize_land(v___x_92_, v___x_95_);
v___x_97_ = lean_array_uget_borrowed(v_x_75_, v___x_96_);
lean_inc(v___x_97_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 2, v___x_97_);
v___x_99_ = v___x_81_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_key_77_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_value_78_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v___x_97_);
v___x_99_ = v_reuseFailAlloc_102_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_array_uset(v_x_75_, v___x_96_, v___x_99_);
v_x_75_ = v___x_100_;
v_x_76_ = v_tail_79_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_106_, lean_object* v_source_107_, lean_object* v_target_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_array_get_size(v_source_107_);
v___x_110_ = lean_nat_dec_lt(v_i_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_source_107_);
lean_dec(v_i_106_);
return v_target_108_;
}
else
{
lean_object* v_es_111_; lean_object* v___x_112_; lean_object* v_source_113_; lean_object* v_target_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_es_111_ = lean_array_fget(v_source_107_, v_i_106_);
v___x_112_ = lean_box(0);
v_source_113_ = lean_array_fset(v_source_107_, v_i_106_, v___x_112_);
v_target_114_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_108_, v_es_111_);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_i_106_, v___x_115_);
lean_dec(v_i_106_);
v_i_106_ = v___x_116_;
v_source_107_ = v_source_113_;
v_target_108_ = v_target_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object* v_data_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_nbuckets_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_119_ = lean_array_get_size(v_data_118_);
v___x_120_ = lean_unsigned_to_nat(2u);
v_nbuckets_121_ = lean_nat_mul(v___x_119_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_box(0);
v___x_124_ = lean_mk_array(v_nbuckets_121_, v___x_123_);
v___x_125_ = lean_array_propagate_mark(v_data_118_, v___x_124_);
v___x_126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v___x_122_, v_data_118_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(lean_object* v_m_127_, lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
lean_object* v_size_130_; lean_object* v_buckets_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_177_; 
v_size_130_ = lean_ctor_get(v_m_127_, 0);
v_buckets_131_ = lean_ctor_get(v_m_127_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_m_127_);
if (v_isSharedCheck_177_ == 0)
{
v___x_133_ = v_m_127_;
v_isShared_134_ = v_isSharedCheck_177_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_buckets_131_);
lean_inc(v_size_130_);
lean_dec(v_m_127_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_177_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; uint64_t v___y_137_; 
v___x_135_ = lean_array_get_size(v_buckets_131_);
if (lean_obj_tag(v_a_128_) == 0)
{
uint64_t v___x_175_; 
v___x_175_ = 1723ULL;
v___y_137_ = v___x_175_;
goto v___jp_136_;
}
else
{
uint64_t v_hash_176_; 
v_hash_176_ = lean_ctor_get_uint64(v_a_128_, sizeof(void*)*2);
v___y_137_ = v_hash_176_;
goto v___jp_136_;
}
v___jp_136_:
{
uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_bkt_149_; uint8_t v___x_150_; 
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___y_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___y_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_135_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v_bkt_149_ = lean_array_uget_borrowed(v_buckets_131_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_128_, v_bkt_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v_size_x27_152_; lean_object* v___x_153_; lean_object* v_buckets_x27_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v_size_x27_152_ = lean_nat_add(v_size_130_, v___x_151_);
lean_dec(v_size_130_);
lean_inc(v_bkt_149_);
v___x_153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_153_, 0, v_a_128_);
lean_ctor_set(v___x_153_, 1, v_b_129_);
lean_ctor_set(v___x_153_, 2, v_bkt_149_);
v_buckets_x27_154_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_mul(v_size_x27_152_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(3u);
v___x_158_ = lean_nat_div(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_array_get_size(v_buckets_x27_154_);
v___x_160_ = lean_nat_dec_le(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
if (v___x_160_ == 0)
{
lean_object* v_val_161_; lean_object* v___x_163_; 
v_val_161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_buckets_x27_154_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_val_161_);
lean_ctor_set(v___x_133_, 0, v_size_x27_152_);
v___x_163_ = v___x_133_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_size_x27_152_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_val_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_166_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_buckets_x27_154_);
lean_ctor_set(v___x_133_, 0, v_size_x27_152_);
v___x_166_ = v___x_133_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_x27_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_buckets_x27_154_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v___x_168_; lean_object* v_buckets_x27_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
lean_inc(v_bkt_149_);
v___x_168_ = lean_box(0);
v_buckets_x27_169_ = lean_array_uset(v_buckets_131_, v___x_148_, v___x_168_);
v___x_170_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_128_, v_b_129_, v_bkt_149_);
v___x_171_ = lean_array_uset(v_buckets_x27_169_, v___x_148_, v___x_170_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_171_);
v___x_173_ = v___x_133_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_size_130_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(lean_object* v_s_178_, lean_object* v_fp_179_){
_start:
{
lean_object* v_prog_180_; lean_object* v___x_181_; 
v_prog_180_ = lean_ctor_get(v_fp_179_, 0);
lean_inc(v_prog_180_);
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(v_s_178_, v_prog_180_, v_fp_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0(lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0___redArg(v_m_183_, v_a_184_, v_b_185_);
return v___x_186_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_188_ = stack[1].m_obj;
lean_object* v_x_189_ = stack[2].m_obj;
uint8_t v_res_191_;
v_res_191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(lean_box(0), v_a_188_, v_x_189_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__0(v_00_u03b2_192_, v_a_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec(v_a_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object* v_00_u03b2_197_, lean_object* v_data_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_data_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object* v_00_u03b2_200_, lean_object* v_a_201_, lean_object* v_b_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_201_, v_b_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_205_, lean_object* v_i_206_, lean_object* v_source_207_, lean_object* v_target_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v_i_206_, v_source_207_, v_target_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_211_, v_x_212_);
return v___x_213_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(lean_object* v_f_214_, lean_object* v_a_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___y_224_; lean_object* v___x_227_; uint8_t v_debug_228_; 
v___x_227_ = lean_st_ref_get(v___y_217_);
v_debug_228_ = lean_ctor_get_uint8(v___x_227_, sizeof(void*)*12);
lean_dec(v___x_227_);
if (v_debug_228_ == 0)
{
v___y_224_ = v___y_217_;
goto v___jp_223_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_214_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec_ref_known(v___x_229_, 1);
v___x_230_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec_ref_known(v___x_230_, 1);
v___y_224_ = v___y_217_;
goto v___jp_223_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_a_215_);
lean_dec_ref(v_f_214_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v_a_215_);
lean_dec_ref(v_f_214_);
v_a_239_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_229_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_229_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_Lean_Expr_app___override(v_f_214_, v_a_215_);
v___x_226_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_225_, v___y_224_);
return v___x_226_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_214_ = stack[0].m_obj;
lean_object* v_a_215_ = stack[1].m_obj;
lean_object* v___y_216_ = stack[2].m_obj;
lean_object* v___y_217_ = stack[3].m_obj;
lean_object* v___y_218_ = stack[4].m_obj;
lean_object* v___y_219_ = stack[5].m_obj;
lean_object* v___y_220_ = stack[6].m_obj;
lean_object* v___y_221_ = stack[7].m_obj;
lean_object* v_res_247_;
v_res_247_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_214_, v_a_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_248_, lean_object* v_a_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_248_, v_a_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_257_;
}
}
lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(lean_object* v_args_258_, lean_object* v_endIdx_259_, lean_object* v_b_260_, lean_object* v_i_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_le(v_endIdx_259_, v_i_261_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_instInhabitedExpr;
v___x_274_ = lean_array_get_borrowed(v___x_273_, v_args_258_, v_i_261_);
lean_inc(v___x_274_);
v___x_275_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_b_260_, v___x_274_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_i_261_, v___x_277_);
lean_dec(v_i_261_);
v_b_260_ = v_a_276_;
v_i_261_ = v___x_278_;
goto _start;
}
else
{
lean_dec(v_i_261_);
return v___x_275_;
}
}
else
{
lean_object* v___x_280_; 
lean_dec(v_i_261_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_b_260_);
return v___x_280_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_258_ = stack[0].m_obj;
lean_object* v_endIdx_259_ = stack[1].m_obj;
lean_object* v_b_260_ = stack[2].m_obj;
lean_object* v_i_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v___y_263_ = stack[5].m_obj;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v___y_265_ = stack[7].m_obj;
lean_object* v___y_266_ = stack[8].m_obj;
lean_object* v___y_267_ = stack[9].m_obj;
lean_object* v___y_268_ = stack[10].m_obj;
lean_object* v___y_269_ = stack[11].m_obj;
lean_object* v___y_270_ = stack[12].m_obj;
lean_object* v_res_281_;
v_res_281_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(v_args_258_, v_endIdx_259_, v_b_260_, v_i_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2___boxed(lean_object* v_args_282_, lean_object* v_endIdx_283_, lean_object* v_b_284_, lean_object* v_i_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(v_args_282_, v_endIdx_283_, v_b_284_, v_i_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec(v_endIdx_283_);
lean_dec_ref(v_args_282_);
return v_res_296_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(lean_object* v_f_297_, lean_object* v_args_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get_size(v_args_298_);
v___x_311_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2(v_args_298_, v___x_310_, v_f_297_, v___x_309_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_297_ = stack[0].m_obj;
lean_object* v_args_298_ = stack[1].m_obj;
lean_object* v___y_299_ = stack[2].m_obj;
lean_object* v___y_300_ = stack[3].m_obj;
lean_object* v___y_301_ = stack[4].m_obj;
lean_object* v___y_302_ = stack[5].m_obj;
lean_object* v___y_303_ = stack[6].m_obj;
lean_object* v___y_304_ = stack[7].m_obj;
lean_object* v___y_305_ = stack[8].m_obj;
lean_object* v___y_306_ = stack[9].m_obj;
lean_object* v___y_307_ = stack[10].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_f_297_, v_args_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1___boxed(lean_object* v_f_313_, lean_object* v_args_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_f_313_, v_args_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v_args_314_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_ks_330_; lean_object* v_vs_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_355_; 
v_ks_330_ = lean_ctor_get(v_x_326_, 0);
v_vs_331_ = lean_ctor_get(v_x_326_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_355_ == 0)
{
v___x_333_ = v_x_326_;
v_isShared_334_ = v_isSharedCheck_355_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_vs_331_);
lean_inc(v_ks_330_);
lean_dec(v_x_326_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_355_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_array_get_size(v_ks_330_);
v___x_336_ = lean_nat_dec_lt(v_x_327_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec(v_x_327_);
v___x_337_ = lean_array_push(v_ks_330_, v_x_328_);
v___x_338_ = lean_array_push(v_vs_331_, v_x_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_338_);
lean_ctor_set(v___x_333_, 0, v___x_337_);
v___x_340_ = v___x_333_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
else
{
lean_object* v_k_x27_342_; uint8_t v___x_343_; 
v_k_x27_342_ = lean_array_fget_borrowed(v_ks_330_, v_x_327_);
v___x_343_ = l_Lean_instBEqMVarId_beq(v_x_328_, v_k_x27_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_345_; 
if (v_isShared_334_ == 0)
{
v___x_345_ = v___x_333_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_ks_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_vs_331_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_x_327_, v___x_346_);
lean_dec(v_x_327_);
v_x_326_ = v___x_345_;
v_x_327_ = v___x_347_;
goto _start;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_array_fset(v_ks_330_, v_x_327_, v_x_328_);
v___x_351_ = lean_array_fset(v_vs_331_, v_x_327_, v_x_329_);
lean_dec(v_x_327_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_351_);
lean_ctor_set(v___x_333_, 0, v___x_350_);
v___x_353_ = v___x_333_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_n_356_, lean_object* v_k_357_, lean_object* v_v_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_n_356_, v___x_359_, v_k_357_, v_v_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_361_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(lean_object* v_x_362_, size_t v_x_363_, size_t v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_object* v_es_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v_j_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_es_367_ = lean_ctor_get(v_x_362_, 0);
v___x_368_ = ((size_t)31ULL);
v___x_369_ = lean_usize_land(v_x_363_, v___x_368_);
v_j_370_ = lean_usize_to_nat(v___x_369_);
v___x_371_ = lean_array_get_size(v_es_367_);
v___x_372_ = lean_nat_dec_lt(v_j_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec(v_j_370_);
lean_dec(v_x_366_);
lean_dec(v_x_365_);
return v_x_362_;
}
else
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_411_; 
lean_inc_ref(v_es_367_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_x_362_, 0);
lean_dec(v_unused_412_);
v___x_374_ = v_x_362_;
v_isShared_375_ = v_isSharedCheck_411_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_411_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_v_376_; lean_object* v___x_377_; lean_object* v_xs_x27_378_; lean_object* v___y_380_; 
v_v_376_ = lean_array_fget(v_es_367_, v_j_370_);
v___x_377_ = lean_box(0);
v_xs_x27_378_ = lean_array_fset(v_es_367_, v_j_370_, v___x_377_);
switch(lean_obj_tag(v_v_376_))
{
case 0:
{
lean_object* v_key_385_; lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v_key_385_ = lean_ctor_get(v_v_376_, 0);
v_val_386_ = lean_ctor_get(v_v_376_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_v_376_);
if (v_isSharedCheck_396_ == 0)
{
v___x_388_ = v_v_376_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_inc(v_key_385_);
lean_dec(v_v_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v___x_390_; 
v___x_390_ = l_Lean_instBEqMVarId_beq(v_x_365_, v_key_385_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_del_object(v___x_388_);
v___x_391_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_385_, v_val_386_, v_x_365_, v_x_366_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___y_380_ = v___x_392_;
goto v___jp_379_;
}
else
{
lean_object* v___x_394_; 
lean_dec(v_val_386_);
lean_dec(v_key_385_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_x_366_);
lean_ctor_set(v___x_388_, 0, v_x_365_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_x_365_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_x_366_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v___y_380_ = v___x_394_;
goto v___jp_379_;
}
}
}
}
case 1:
{
lean_object* v_node_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_409_; 
v_node_397_ = lean_ctor_get(v_v_376_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_v_376_);
if (v_isSharedCheck_409_ == 0)
{
v___x_399_ = v_v_376_;
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_node_397_);
lean_dec(v_v_376_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_401_ = ((size_t)5ULL);
v___x_402_ = lean_usize_shift_right(v_x_363_, v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_x_364_, v___x_403_);
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_node_397_, v___x_402_, v___x_404_, v_x_365_, v_x_366_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_405_);
v___x_407_ = v___x_399_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_380_ = v___x_407_;
goto v___jp_379_;
}
}
}
default: 
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_x_365_);
lean_ctor_set(v___x_410_, 1, v_x_366_);
v___y_380_ = v___x_410_;
goto v___jp_379_;
}
}
v___jp_379_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_array_fset(v_xs_x27_378_, v_j_370_, v___y_380_);
lean_dec(v_j_370_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_381_);
v___x_383_ = v___x_374_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
else
{
lean_object* v_ks_413_; lean_object* v_vs_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_432_; 
v_ks_413_ = lean_ctor_get(v_x_362_, 0);
v_vs_414_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_432_ == 0)
{
v___x_416_ = v_x_362_;
v_isShared_417_ = v_isSharedCheck_432_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_vs_414_);
lean_inc(v_ks_413_);
lean_dec(v_x_362_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_432_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_ks_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_vs_414_);
v___x_419_ = v_reuseFailAlloc_431_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v_newNode_420_; size_t v___x_421_; uint8_t v___x_422_; 
v_newNode_420_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(v___x_419_, v_x_365_, v_x_366_);
v___x_421_ = ((size_t)7ULL);
v___x_422_ = lean_usize_dec_le(v___x_421_, v_x_364_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_423_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_420_);
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = lean_nat_dec_lt(v___x_423_, v___x_424_);
lean_dec(v___x_423_);
if (v___x_425_ == 0)
{
lean_object* v_ks_426_; lean_object* v_vs_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_ks_426_ = lean_ctor_get(v_newNode_420_, 0);
lean_inc_ref(v_ks_426_);
v_vs_427_ = lean_ctor_get(v_newNode_420_, 1);
lean_inc_ref(v_vs_427_);
lean_dec_ref(v_newNode_420_);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_430_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_x_364_, v_ks_426_, v_vs_427_, v___x_428_, v___x_429_);
lean_dec_ref(v_vs_427_);
lean_dec_ref(v_ks_426_);
return v___x_430_;
}
else
{
return v_newNode_420_;
}
}
else
{
return v_newNode_420_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_362_ = stack[0].m_obj;
size_t v_x_363_ = stack[1].m_num;
size_t v_x_364_ = stack[2].m_num;
lean_object* v_x_365_ = stack[3].m_obj;
lean_object* v_x_366_ = stack[4].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_362_, v_x_363_, v_x_364_, v_x_365_, v_x_366_);
stack->m_obj
 = v_res_433_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(size_t v_depth_434_, lean_object* v_keys_435_, lean_object* v_vals_436_, lean_object* v_i_437_, lean_object* v_entries_438_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_array_get_size(v_keys_435_);
v___x_440_ = lean_nat_dec_lt(v_i_437_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v_i_437_);
return v_entries_438_;
}
else
{
lean_object* v_k_441_; lean_object* v_v_442_; uint64_t v___x_443_; size_t v_h_444_; size_t v___x_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v_h_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_k_441_ = lean_array_fget_borrowed(v_keys_435_, v_i_437_);
v_v_442_ = lean_array_fget_borrowed(v_vals_436_, v_i_437_);
v___x_443_ = l_Lean_instHashableMVarId_hash(v_k_441_);
v_h_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = ((size_t)5ULL);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_sub(v_depth_434_, v___x_447_);
v___x_449_ = lean_usize_mul(v___x_445_, v___x_448_);
v_h_450_ = lean_usize_shift_right(v_h_444_, v___x_449_);
v___x_451_ = lean_nat_add(v_i_437_, v___x_446_);
lean_dec(v_i_437_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
v___x_452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_entries_438_, v_h_450_, v_depth_434_, v_k_441_, v_v_442_);
v_i_437_ = v___x_451_;
v_entries_438_ = v___x_452_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_434_ = stack[0].m_num;
lean_object* v_keys_435_ = stack[1].m_obj;
lean_object* v_vals_436_ = stack[2].m_obj;
lean_object* v_i_437_ = stack[3].m_obj;
lean_object* v_entries_438_ = stack[4].m_obj;
lean_object* v_res_454_;
v_res_454_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_434_, v_keys_435_, v_vals_436_, v_i_437_, v_entries_438_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg___boxed(lean_object* v_depth_455_, lean_object* v_keys_456_, lean_object* v_vals_457_, lean_object* v_i_458_, lean_object* v_entries_459_){
_start:
{
size_t v_depth_boxed_460_; lean_object* v_res_461_; 
v_depth_boxed_460_ = lean_unbox_usize(v_depth_455_);
lean_dec(v_depth_455_);
v_res_461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_boxed_460_, v_keys_456_, v_vals_457_, v_i_458_, v_entries_459_);
lean_dec_ref(v_vals_457_);
lean_dec_ref(v_keys_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
size_t v_x_33219__boxed_467_; size_t v_x_33220__boxed_468_; lean_object* v_res_469_; 
v_x_33219__boxed_467_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_x_33220__boxed_468_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_462_, v_x_33219__boxed_467_, v_x_33220__boxed_468_, v_x_465_, v_x_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint64_t v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_473_ = l_Lean_instHashableMVarId_hash(v_x_471_);
v___x_474_ = lean_uint64_to_usize(v___x_473_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_470_, v___x_474_, v___x_475_, v_x_471_, v_x_472_);
return v___x_476_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(lean_object* v_mvarId_477_, lean_object* v_val_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_cache_483_; lean_object* v_zetaDeltaFVarIds_484_; lean_object* v_postponed_485_; lean_object* v_diag_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_516_; 
v___x_481_ = lean_st_ref_take(v___y_479_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_cache_483_ = lean_ctor_get(v___x_481_, 1);
v_zetaDeltaFVarIds_484_ = lean_ctor_get(v___x_481_, 2);
v_postponed_485_ = lean_ctor_get(v___x_481_, 3);
v_diag_486_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_516_ == 0)
{
v___x_488_ = v___x_481_;
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_diag_486_);
lean_inc(v_postponed_485_);
lean_inc(v_zetaDeltaFVarIds_484_);
lean_inc(v_cache_483_);
lean_inc(v_mctx_482_);
lean_dec(v___x_481_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_depth_490_; lean_object* v_levelAssignDepth_491_; lean_object* v_lmvarCounter_492_; lean_object* v_mvarCounter_493_; lean_object* v_lDecls_494_; lean_object* v_decls_495_; lean_object* v_userNames_496_; lean_object* v_lAssignment_497_; lean_object* v_eAssignment_498_; lean_object* v_dAssignment_499_; lean_object* v_instanceTypedMVars_500_; lean_object* v_synthNormMemo_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_515_; 
v_depth_490_ = lean_ctor_get(v_mctx_482_, 0);
v_levelAssignDepth_491_ = lean_ctor_get(v_mctx_482_, 1);
v_lmvarCounter_492_ = lean_ctor_get(v_mctx_482_, 2);
v_mvarCounter_493_ = lean_ctor_get(v_mctx_482_, 3);
v_lDecls_494_ = lean_ctor_get(v_mctx_482_, 4);
v_decls_495_ = lean_ctor_get(v_mctx_482_, 5);
v_userNames_496_ = lean_ctor_get(v_mctx_482_, 6);
v_lAssignment_497_ = lean_ctor_get(v_mctx_482_, 7);
v_eAssignment_498_ = lean_ctor_get(v_mctx_482_, 8);
v_dAssignment_499_ = lean_ctor_get(v_mctx_482_, 9);
v_instanceTypedMVars_500_ = lean_ctor_get(v_mctx_482_, 10);
v_synthNormMemo_501_ = lean_ctor_get(v_mctx_482_, 11);
v_isSharedCheck_515_ = !lean_is_exclusive(v_mctx_482_);
if (v_isSharedCheck_515_ == 0)
{
v___x_503_ = v_mctx_482_;
v_isShared_504_ = v_isSharedCheck_515_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_synthNormMemo_501_);
lean_inc(v_instanceTypedMVars_500_);
lean_inc(v_dAssignment_499_);
lean_inc(v_eAssignment_498_);
lean_inc(v_lAssignment_497_);
lean_inc(v_userNames_496_);
lean_inc(v_decls_495_);
lean_inc(v_lDecls_494_);
lean_inc(v_mvarCounter_493_);
lean_inc(v_lmvarCounter_492_);
lean_inc(v_levelAssignDepth_491_);
lean_inc(v_depth_490_);
lean_dec(v_mctx_482_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_515_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = lean_box(0);
v___x_506_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_eAssignment_498_, v_mvarId_477_, v_val_478_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 8, v___x_506_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_depth_490_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_levelAssignDepth_491_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_lmvarCounter_492_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_mvarCounter_493_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_lDecls_494_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_decls_495_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_userNames_496_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_lAssignment_497_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 9, v_dAssignment_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 10, v_instanceTypedMVars_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 11, v_synthNormMemo_501_);
v___x_508_ = v_reuseFailAlloc_514_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_508_);
v___x_510_ = v___x_488_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_cache_483_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_zetaDeltaFVarIds_484_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_postponed_485_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_diag_486_);
v___x_510_ = v_reuseFailAlloc_513_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_st_ref_put(v___y_479_, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_505_);
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_477_ = stack[0].m_obj;
lean_object* v_val_478_ = stack[1].m_obj;
lean_object* v___y_479_ = stack[2].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_477_, v_val_478_, v___y_479_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg___boxed(lean_object* v_mvarId_518_, lean_object* v_val_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_518_, v_val_519_, v___y_520_);
lean_dec(v___y_520_);
return v_res_522_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(lean_object* v_msgData_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_env_530_; uint8_t v___x_531_; lean_object* v_env_532_; lean_object* v___x_533_; lean_object* v_toCold_534_; lean_object* v_mctx_535_; lean_object* v_lctx_536_; lean_object* v_options_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_env_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_env_530_);
lean_dec(v___x_529_);
v___x_531_ = 0;
v_env_532_ = l_Lean_Environment_setRecordingDeps(v_env_530_, v___x_531_);
v___x_533_ = lean_st_ref_get(v___y_525_);
v_toCold_534_ = lean_ctor_get(v___y_526_, 0);
v_mctx_535_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_mctx_535_);
lean_dec(v___x_533_);
v_lctx_536_ = lean_ctor_get(v___y_524_, 2);
v_options_537_ = lean_ctor_get(v_toCold_534_, 2);
lean_inc_ref(v_options_537_);
lean_inc_ref(v_lctx_536_);
v___x_538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_538_, 0, v_env_532_);
lean_ctor_set(v___x_538_, 1, v_mctx_535_);
lean_ctor_set(v___x_538_, 2, v_lctx_536_);
lean_ctor_set(v___x_538_, 3, v_options_537_);
v___x_539_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_msgData_523_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_523_ = stack[0].m_obj;
lean_object* v___y_524_ = stack[1].m_obj;
lean_object* v___y_525_ = stack[2].m_obj;
lean_object* v___y_526_ = stack[3].m_obj;
lean_object* v___y_527_ = stack[4].m_obj;
lean_object* v_res_541_;
v_res_541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msgData_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5___boxed(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msgData_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_ref_555_; lean_object* v___x_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_ref_555_ = lean_ctor_get(v___y_552_, 2);
v___x_556_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_inc(v_ref_555_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_ref_555_);
lean_ctor_set(v___x_561_, 1, v_a_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 1);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_549_ = stack[0].m_obj;
lean_object* v___y_550_ = stack[1].m_obj;
lean_object* v___y_551_ = stack[2].m_obj;
lean_object* v___y_552_ = stack[3].m_obj;
lean_object* v___y_553_ = stack[4].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg___boxed(lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_573_;
}
}
lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(lean_object* v_goal_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_goal_574_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_x_576_);
return v___x_587_;
}
else
{
lean_object* v_head_588_; lean_object* v_tail_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_612_; 
v_head_588_ = lean_ctor_get(v_x_575_, 0);
v_tail_589_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_612_ == 0)
{
v___x_591_ = v_x_575_;
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_tail_589_);
lean_inc(v_head_588_);
lean_dec(v_x_575_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; 
lean_inc(v_head_588_);
v___x_593_ = l_Lean_MVarId_getType(v_head_588_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_Expr_appArg_x21(v_a_594_);
lean_dec(v_a_594_);
v___x_596_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v___x_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_598_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_x_576_);
v___x_598_ = v___x_591_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_head_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_x_576_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v_x_575_ = v_tail_589_;
v_x_576_ = v___x_598_;
goto _start;
}
}
else
{
lean_object* v_specProof_601_; lean_object* v___x_602_; 
lean_dec_ref_known(v___x_596_, 1);
lean_del_object(v___x_591_);
v_specProof_601_ = lean_ctor_get(v_goal_574_, 5);
lean_inc_ref(v_specProof_601_);
v___x_602_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_head_588_, v_specProof_601_, v___y_583_);
lean_dec_ref(v___x_602_);
v_x_575_ = v_tail_589_;
goto _start;
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_591_);
lean_dec(v_tail_589_);
lean_dec(v_head_588_);
lean_dec(v_x_576_);
lean_dec_ref(v_goal_574_);
v_a_604_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_593_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_574_ = stack[0].m_obj;
lean_object* v_x_575_ = stack[1].m_obj;
lean_object* v_x_576_ = stack[2].m_obj;
lean_object* v___y_577_ = stack[3].m_obj;
lean_object* v___y_578_ = stack[4].m_obj;
lean_object* v___y_579_ = stack[5].m_obj;
lean_object* v___y_580_ = stack[6].m_obj;
lean_object* v___y_581_ = stack[7].m_obj;
lean_object* v___y_582_ = stack[8].m_obj;
lean_object* v___y_583_ = stack[9].m_obj;
lean_object* v___y_584_ = stack[10].m_obj;
lean_object* v___y_585_ = stack[11].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_574_, v_x_575_, v_x_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2___boxed(lean_object* v_goal_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_614_, v_x_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
return v_res_627_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(lean_object* v_frame_631_, lean_object* v_pre_632_, lean_object* v_mkOpApp_633_, lean_object* v_excessArgs_634_, lean_object* v_le_635_, lean_object* v_goal_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Sym_shareCommon(v_frame_631_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v_frame_649_; lean_object* v_footprint_650_; lean_object* v_framedApp_651_; lean_object* v_splitLatticeOp_x3f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_n(v_a_648_, 2);
lean_dec_ref_known(v___x_647_, 1);
v_frame_649_ = lean_ctor_get(v_goal_636_, 0);
v_footprint_650_ = lean_ctor_get(v_goal_636_, 1);
v_framedApp_651_ = lean_ctor_get(v_goal_636_, 2);
v_splitLatticeOp_x3f_652_ = lean_ctor_get(v_goal_636_, 6);
lean_inc(v_frame_649_);
v___x_653_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_frame_649_, v_a_648_, v___y_643_);
lean_dec_ref(v___x_653_);
lean_inc_ref(v_pre_632_);
lean_inc(v_footprint_650_);
v___x_654_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_footprint_650_, v_pre_632_, v___y_643_);
lean_dec_ref(v___x_654_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
v___x_655_ = lean_apply_7(v_mkOpApp_633_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_Elab_Tactic_VCGen_WPApp_wp(v_framedApp_651_);
v___x_658_ = lean_unsigned_to_nat(2u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
lean_inc_ref(v___x_659_);
v___x_660_ = lean_array_push(v___x_659_, v_a_648_);
v___x_661_ = lean_array_push(v___x_660_, v___x_657_);
v___x_662_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_656_, v___x_661_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v___x_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_663_, v_excessArgs_634_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = lean_array_push(v___x_659_, v_pre_632_);
v___x_667_ = lean_array_push(v___x_666_, v_a_665_);
v___x_668_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_le_635_, v___x_667_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_box(0);
v___x_671_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_669_, v___x_670_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_721_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_721_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_721_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_721_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_a_677_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = l_Lean_Expr_mvarId_x21(v_a_672_);
lean_inc_ref(v_splitLatticeOp_x3f_652_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc(v___x_682_);
v___x_683_ = lean_apply_11(v_splitLatticeOp_x3f_652_, v___x_682_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, lean_box(0));
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
if (lean_obj_tag(v_a_684_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___x_682_);
v_val_685_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v_a_684_, 1);
v___x_686_ = lean_box(0);
v___x_687_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_636_, v_val_685_, v___x_686_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_List_reverse___redArg(v_a_688_);
v_a_677_ = v___x_689_;
goto v___jp_676_;
}
else
{
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_687_, 1);
v_a_677_ = v_a_690_;
goto v___jp_676_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
v_a_691_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_687_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_a_684_);
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec_ref(v_goal_636_);
v___x_699_ = l_Lean_MVarId_getType(v___x_682_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1);
v___x_702_ = l_Lean_indentExpr(v_a_700_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v___x_703_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_704_;
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_699_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v___x_682_);
lean_del_object(v___x_674_);
lean_dec(v_a_672_);
lean_dec_ref(v_goal_636_);
v_a_713_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_683_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_683_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_672_);
lean_ctor_set(v___x_678_, 1, v_a_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_goal_636_);
v_a_722_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_671_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_671_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_goal_636_);
v_a_730_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_668_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_668_);
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
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_659_);
lean_dec_ref(v_goal_636_);
lean_dec_ref(v_le_635_);
lean_dec_ref(v_pre_632_);
v_a_738_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_664_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_664_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___x_659_);
lean_dec_ref(v_goal_636_);
lean_dec_ref(v_le_635_);
lean_dec_ref(v_pre_632_);
v_a_746_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_662_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_662_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_648_);
lean_dec_ref(v_goal_636_);
lean_dec_ref(v_le_635_);
lean_dec_ref(v_pre_632_);
v_a_754_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_655_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_655_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_goal_636_);
lean_dec_ref(v_le_635_);
lean_dec_ref(v_mkOpApp_633_);
lean_dec_ref(v_pre_632_);
v_a_762_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_647_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_647_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_frame_631_ = stack[0].m_obj;
lean_object* v_pre_632_ = stack[1].m_obj;
lean_object* v_mkOpApp_633_ = stack[2].m_obj;
lean_object* v_excessArgs_634_ = stack[3].m_obj;
lean_object* v_le_635_ = stack[4].m_obj;
lean_object* v_goal_636_ = stack[5].m_obj;
lean_object* v___y_637_ = stack[6].m_obj;
lean_object* v___y_638_ = stack[7].m_obj;
lean_object* v___y_639_ = stack[8].m_obj;
lean_object* v___y_640_ = stack[9].m_obj;
lean_object* v___y_641_ = stack[10].m_obj;
lean_object* v___y_642_ = stack[11].m_obj;
lean_object* v___y_643_ = stack[12].m_obj;
lean_object* v___y_644_ = stack[13].m_obj;
lean_object* v___y_645_ = stack[14].m_obj;
lean_object* v_res_770_;
v_res_770_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(v_frame_631_, v_pre_632_, v_mkOpApp_633_, v_excessArgs_634_, v_le_635_, v_goal_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed(lean_object* v_frame_771_, lean_object* v_pre_772_, lean_object* v_mkOpApp_773_, lean_object* v_excessArgs_774_, lean_object* v_le_775_, lean_object* v_goal_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(v_frame_771_, v_pre_772_, v_mkOpApp_773_, v_excessArgs_774_, v_le_775_, v_goal_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v_excessArgs_774_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(lean_object* v_i_788_, lean_object* v_frame_789_){
_start:
{
lean_object* v_unframedApp_790_; lean_object* v_pre_791_; lean_object* v_le_792_; lean_object* v_mkOpApp_793_; lean_object* v_excessArgs_794_; lean_object* v___f_795_; lean_object* v___x_796_; 
v_unframedApp_790_ = lean_ctor_get(v_i_788_, 2);
lean_inc_ref(v_unframedApp_790_);
v_pre_791_ = lean_ctor_get(v_i_788_, 0);
lean_inc_ref(v_pre_791_);
v_le_792_ = lean_ctor_get(v_i_788_, 1);
lean_inc_ref(v_le_792_);
v_mkOpApp_793_ = lean_ctor_get(v_i_788_, 5);
lean_inc_ref(v_mkOpApp_793_);
lean_dec_ref(v_i_788_);
v_excessArgs_794_ = lean_ctor_get(v_unframedApp_790_, 3);
lean_inc_ref_n(v_excessArgs_794_, 2);
lean_dec_ref(v_unframedApp_790_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed), 16, 5);
lean_closure_set(v___f_795_, 0, v_frame_789_);
lean_closure_set(v___f_795_, 1, v_pre_791_);
lean_closure_set(v___f_795_, 2, v_mkOpApp_793_);
lean_closure_set(v___f_795_, 3, v_excessArgs_794_);
lean_closure_set(v___f_795_, 4, v_le_792_);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v_excessArgs_794_);
lean_ctor_set(v___x_796_, 1, v___f_795_);
return v___x_796_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(lean_object* v_mvarId_797_, lean_object* v_val_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_797_, v_val_798_, v___y_805_);
return v___x_809_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_797_ = stack[0].m_obj;
lean_object* v_val_798_ = stack[1].m_obj;
lean_object* v___y_799_ = stack[2].m_obj;
lean_object* v___y_800_ = stack[3].m_obj;
lean_object* v___y_801_ = stack[4].m_obj;
lean_object* v___y_802_ = stack[5].m_obj;
lean_object* v___y_803_ = stack[6].m_obj;
lean_object* v___y_804_ = stack[7].m_obj;
lean_object* v___y_805_ = stack[8].m_obj;
lean_object* v___y_806_ = stack[9].m_obj;
lean_object* v___y_807_ = stack[10].m_obj;
lean_object* v_res_810_;
v_res_810_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(v_mvarId_797_, v_val_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___boxed(lean_object* v_mvarId_811_, lean_object* v_val_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(v_mvarId_811_, v_val_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
return v_res_823_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(lean_object* v_00_u03b1_824_, lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_825_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_825_ = stack[1].m_obj;
lean_object* v___y_826_ = stack[2].m_obj;
lean_object* v___y_827_ = stack[3].m_obj;
lean_object* v___y_828_ = stack[4].m_obj;
lean_object* v___y_829_ = stack[5].m_obj;
lean_object* v___y_830_ = stack[6].m_obj;
lean_object* v___y_831_ = stack[7].m_obj;
lean_object* v___y_832_ = stack[8].m_obj;
lean_object* v___y_833_ = stack[9].m_obj;
lean_object* v___y_834_ = stack[10].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(lean_box(0), v_msg_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___boxed(lean_object* v_00_u03b1_838_, lean_object* v_msg_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(v_00_u03b1_838_, v_msg_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0(lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(lean_object* v_f_856_, lean_object* v_a_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_856_, v_a_857_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v___x_868_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_856_ = stack[0].m_obj;
lean_object* v_a_857_ = stack[1].m_obj;
lean_object* v___y_858_ = stack[2].m_obj;
lean_object* v___y_859_ = stack[3].m_obj;
lean_object* v___y_860_ = stack[4].m_obj;
lean_object* v___y_861_ = stack[5].m_obj;
lean_object* v___y_862_ = stack[6].m_obj;
lean_object* v___y_863_ = stack[7].m_obj;
lean_object* v___y_864_ = stack[8].m_obj;
lean_object* v___y_865_ = stack[9].m_obj;
lean_object* v___y_866_ = stack[10].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(v_f_856_, v_a_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___boxed(lean_object* v_f_870_, lean_object* v_a_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(v_f_870_, v_a_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
return v_res_882_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, size_t v_x_885_, size_t v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_884_, v_x_885_, v_x_886_, v_x_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_884_ = stack[1].m_obj;
size_t v_x_885_ = stack[2].m_num;
size_t v_x_886_ = stack[3].m_num;
lean_object* v_x_887_ = stack[4].m_obj;
lean_object* v_x_888_ = stack[5].m_obj;
lean_object* v_res_890_;
v_res_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(lean_box(0), v_x_884_, v_x_885_, v_x_886_, v_x_887_, v_x_888_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
size_t v_x_34379__boxed_897_; size_t v_x_34380__boxed_898_; lean_object* v_res_899_; 
v_x_34379__boxed_897_ = lean_unbox_usize(v_x_893_);
lean_dec(v_x_893_);
v_x_34380__boxed_898_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_res_899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(v_00_u03b2_891_, v_x_892_, v_x_34379__boxed_897_, v_x_34380__boxed_898_, v_x_895_, v_x_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_900_, lean_object* v_n_901_, lean_object* v_k_902_, lean_object* v_v_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(v_n_901_, v_k_902_, v_v_903_);
return v___x_904_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_905_, size_t v_depth_906_, lean_object* v_keys_907_, lean_object* v_vals_908_, lean_object* v_heq_909_, lean_object* v_i_910_, lean_object* v_entries_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_906_, v_keys_907_, v_vals_908_, v_i_910_, v_entries_911_);
return v___x_912_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_depth_906_ = stack[1].m_num;
lean_object* v_keys_907_ = stack[2].m_obj;
lean_object* v_vals_908_ = stack[3].m_obj;
lean_object* v_i_910_ = stack[5].m_obj;
lean_object* v_entries_911_ = stack[6].m_obj;
lean_object* v_res_913_;
v_res_913_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(lean_box(0), v_depth_906_, v_keys_907_, v_vals_908_, lean_box(0), v_i_910_, v_entries_911_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b2_914_, lean_object* v_depth_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_heq_918_, lean_object* v_i_919_, lean_object* v_entries_920_){
_start:
{
size_t v_depth_boxed_921_; lean_object* v_res_922_; 
v_depth_boxed_921_ = lean_unbox_usize(v_depth_915_);
lean_dec(v_depth_915_);
v_res_922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(v_00_u03b2_914_, v_depth_boxed_921_, v_keys_916_, v_vals_917_, v_heq_918_, v_i_919_, v_entries_920_);
lean_dec_ref(v_vals_917_);
lean_dec_ref(v_keys_916_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b2_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_x_924_, v_x_925_, v_x_926_, v_x_927_);
return v___x_928_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(lean_object* v_i_929_){
_start:
{
lean_object* v_providedFrame_x3f_931_; 
v_providedFrame_x3f_931_ = lean_ctor_get(v_i_929_, 3);
lean_inc(v_providedFrame_x3f_931_);
if (lean_obj_tag(v_providedFrame_x3f_931_) == 1)
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_val_932_ = lean_ctor_get(v_providedFrame_x3f_931_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_providedFrame_x3f_931_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_providedFrame_x3f_931_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v_providedFrame_x3f_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(v_i_929_, v_val_932_);
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 0);
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_providedFrame_x3f_931_);
lean_dec_ref(v_i_929_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_929_ = stack[0].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_929_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg___boxed(lean_object* v_i_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_944_);
return v_res_946_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(lean_object* v_i_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_947_);
return v___x_958_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_947_ = stack[0].m_obj;
lean_object* v_a_948_ = stack[1].m_obj;
lean_object* v_a_949_ = stack[2].m_obj;
lean_object* v_a_950_ = stack[3].m_obj;
lean_object* v_a_951_ = stack[4].m_obj;
lean_object* v_a_952_ = stack[5].m_obj;
lean_object* v_a_953_ = stack[6].m_obj;
lean_object* v_a_954_ = stack[7].m_obj;
lean_object* v_a_955_ = stack[8].m_obj;
lean_object* v_a_956_ = stack[9].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(v_i_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed(lean_object* v_i_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(v_i_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
return v_res_971_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(lean_object* v_info_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_986_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_979_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_unsigned_to_nat(2u);
v___x_990_ = lean_mk_empty_array_with_capacity(v___x_989_);
v___x_991_ = lean_array_push(v___x_990_, v___x_987_);
v___x_992_ = lean_array_push(v___x_991_, v___x_988_);
v___x_993_ = l_Lean_Meta_mkAppOptM(v___x_985_, v___x_992_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_993_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_979_ = stack[0].m_obj;
lean_object* v_a_980_ = stack[1].m_obj;
lean_object* v_a_981_ = stack[2].m_obj;
lean_object* v_a_982_ = stack[3].m_obj;
lean_object* v_a_983_ = stack[4].m_obj;
lean_object* v_res_994_;
v_res_994_ = l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(v_info_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___boxed(lean_object* v_info_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(v_info_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec_ref(v_info_995_);
return v_res_1001_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(lean_object* v_info_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_1002_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1002_ = stack[0].m_obj;
lean_object* v___y_1003_ = stack[1].m_obj;
lean_object* v___y_1004_ = stack[2].m_obj;
lean_object* v___y_1005_ = stack[3].m_obj;
lean_object* v___y_1006_ = stack[4].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(v_info_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0___boxed(lean_object* v_info_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(v_info_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_info_1011_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1020_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed), 11, 0);
v___f_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0));
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1));
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
lean_ctor_set(v___x_1024_, 2, v___x_1022_);
lean_ctor_set(v___x_1024_, 3, v___f_1021_);
lean_ctor_set(v___x_1024_, 4, v___x_1020_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc(void){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2, &l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2);
return v___x_1025_;
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
