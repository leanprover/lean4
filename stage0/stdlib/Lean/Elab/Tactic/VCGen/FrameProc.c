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
v_debug_226_ = lean_ctor_get_uint8(v___x_225_, sizeof(void*)*11);
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
size_t v_x_33093__boxed_460_; size_t v_x_33094__boxed_461_; lean_object* v_res_462_; 
v_x_33093__boxed_460_ = lean_unbox_usize(v_x_456_);
lean_dec(v_x_456_);
v_x_33094__boxed_461_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_res_462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_455_, v_x_33093__boxed_460_, v_x_33094__boxed_461_, v_x_458_, v_x_459_);
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
lean_object* v___x_474_; lean_object* v_mctx_475_; lean_object* v_cache_476_; lean_object* v_zetaDeltaFVarIds_477_; lean_object* v_postponed_478_; lean_object* v_diag_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_508_; 
v___x_474_ = lean_st_ref_take(v___y_472_);
v_mctx_475_ = lean_ctor_get(v___x_474_, 0);
v_cache_476_ = lean_ctor_get(v___x_474_, 1);
v_zetaDeltaFVarIds_477_ = lean_ctor_get(v___x_474_, 2);
v_postponed_478_ = lean_ctor_get(v___x_474_, 3);
v_diag_479_ = lean_ctor_get(v___x_474_, 4);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_508_ == 0)
{
v___x_481_ = v___x_474_;
v_isShared_482_ = v_isSharedCheck_508_;
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
v_isShared_482_ = v_isSharedCheck_508_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_depth_483_; lean_object* v_levelAssignDepth_484_; lean_object* v_lmvarCounter_485_; lean_object* v_mvarCounter_486_; lean_object* v_lDecls_487_; lean_object* v_decls_488_; lean_object* v_userNames_489_; lean_object* v_lAssignment_490_; lean_object* v_eAssignment_491_; lean_object* v_dAssignment_492_; lean_object* v_instanceTypedMVars_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_507_; 
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
v_isSharedCheck_507_ = !lean_is_exclusive(v_mctx_475_);
if (v_isSharedCheck_507_ == 0)
{
v___x_495_ = v_mctx_475_;
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
else
{
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
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = lean_box(0);
v___x_498_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_eAssignment_491_, v_mvarId_470_, v_val_471_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 8, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_depth_483_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_levelAssignDepth_484_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_lmvarCounter_485_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_mvarCounter_486_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_lDecls_487_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_decls_488_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_userNames_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_lAssignment_490_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_506_, 9, v_dAssignment_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 10, v_instanceTypedMVars_493_);
v___x_500_ = v_reuseFailAlloc_506_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_500_);
v___x_502_ = v___x_481_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_cache_476_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_zetaDeltaFVarIds_477_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_postponed_478_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_diag_479_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_st_ref_put(v___y_472_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_497_);
return v___x_504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg___boxed(lean_object* v_mvarId_509_, lean_object* v_val_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_509_, v_val_510_, v___y_511_);
lean_dec(v___y_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(lean_object* v_msgData_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; lean_object* v_env_523_; lean_object* v___x_524_; lean_object* v_toCold_525_; lean_object* v_mctx_526_; lean_object* v_lctx_527_; lean_object* v_options_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_520_ = lean_st_ref_get(v___y_518_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = 0;
v_env_523_ = l_Lean_Environment_setRecordingDeps(v_env_521_, v___x_522_);
v___x_524_ = lean_st_ref_get(v___y_516_);
v_toCold_525_ = lean_ctor_get(v___y_517_, 0);
v_mctx_526_ = lean_ctor_get(v___x_524_, 0);
lean_inc_ref(v_mctx_526_);
lean_dec(v___x_524_);
v_lctx_527_ = lean_ctor_get(v___y_515_, 2);
v_options_528_ = lean_ctor_get(v_toCold_525_, 2);
lean_inc_ref(v_options_528_);
lean_inc_ref(v_lctx_527_);
v___x_529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_529_, 0, v_env_523_);
lean_ctor_set(v___x_529_, 1, v_mctx_526_);
lean_ctor_set(v___x_529_, 2, v_lctx_527_);
lean_ctor_set(v___x_529_, 3, v_options_528_);
v___x_530_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_msgData_514_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5___boxed(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msgData_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_ref_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_ref_545_ = lean_ctor_get(v___y_542_, 2);
v___x_546_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3_spec__5(v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_ref_545_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_ref_545_);
lean_ctor_set(v___x_551_, 1, v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg___boxed(lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(lean_object* v_goal_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v_goal_563_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_x_565_);
return v___x_576_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_head_577_ = lean_ctor_get(v_x_564_, 0);
v_tail_578_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_601_ == 0)
{
v___x_580_ = v_x_564_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_tail_578_);
lean_inc(v_head_577_);
lean_dec(v_x_564_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; 
lean_inc(v_head_577_);
v___x_582_ = l_Lean_MVarId_getType(v_head_577_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = l_Lean_Expr_appArg_x21(v_a_583_);
lean_dec(v_a_583_);
v___x_585_ = l_Lean_Elab_Tactic_VCGen_isWPApp_x3f(v___x_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_587_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_x_565_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_head_577_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_x_565_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_x_564_ = v_tail_578_;
v_x_565_ = v___x_587_;
goto _start;
}
}
else
{
lean_object* v_specProof_590_; lean_object* v___x_591_; 
lean_dec_ref_known(v___x_585_, 1);
lean_del_object(v___x_580_);
v_specProof_590_ = lean_ctor_get(v_goal_563_, 5);
lean_inc_ref(v_specProof_590_);
v___x_591_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_head_577_, v_specProof_590_, v___y_572_);
lean_dec_ref(v___x_591_);
v_x_564_ = v_tail_578_;
goto _start;
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_del_object(v___x_580_);
lean_dec(v_tail_578_);
lean_dec(v_head_577_);
lean_dec(v_x_565_);
lean_dec_ref(v_goal_563_);
v_a_593_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_582_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2___boxed(lean_object* v_goal_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_602_, v_x_603_, v_x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__0));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(lean_object* v_frame_619_, lean_object* v_pre_620_, lean_object* v_mkOpApp_621_, lean_object* v_excessArgs_622_, lean_object* v_le_623_, lean_object* v_goal_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Sym_shareCommon(v_frame_619_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_frame_637_; lean_object* v_footprint_638_; lean_object* v_framedApp_639_; lean_object* v_splitLatticeOp_x3f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_n(v_a_636_, 2);
lean_dec_ref_known(v___x_635_, 1);
v_frame_637_ = lean_ctor_get(v_goal_624_, 0);
v_footprint_638_ = lean_ctor_get(v_goal_624_, 1);
v_framedApp_639_ = lean_ctor_get(v_goal_624_, 2);
v_splitLatticeOp_x3f_640_ = lean_ctor_get(v_goal_624_, 6);
lean_inc(v_frame_637_);
v___x_641_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_frame_637_, v_a_636_, v___y_631_);
lean_dec_ref(v___x_641_);
lean_inc_ref(v_pre_620_);
lean_inc(v_footprint_638_);
v___x_642_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_footprint_638_, v_pre_620_, v___y_631_);
lean_dec_ref(v___x_642_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
v___x_643_ = lean_apply_7(v_mkOpApp_621_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, lean_box(0));
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_Elab_Tactic_VCGen_WPApp_wp(v_framedApp_639_);
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = lean_mk_empty_array_with_capacity(v___x_646_);
lean_inc_ref(v___x_647_);
v___x_648_ = lean_array_push(v___x_647_, v_a_636_);
v___x_649_ = lean_array_push(v___x_648_, v___x_645_);
v___x_650_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_644_, v___x_649_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec_ref(v___x_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_a_651_, v_excessArgs_622_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_array_push(v___x_647_, v_pre_620_);
v___x_655_ = lean_array_push(v___x_654_, v_a_653_);
v___x_656_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1(v_le_623_, v___x_655_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec_ref(v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = lean_box(0);
v___x_659_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_657_, v___x_658_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_709_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_709_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_709_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_709_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_a_665_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = l_Lean_Expr_mvarId_x21(v_a_660_);
lean_inc_ref(v_splitLatticeOp_x3f_640_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc(v___y_625_);
lean_inc(v___x_670_);
v___x_671_ = lean_apply_11(v_splitLatticeOp_x3f_640_, v___x_670_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, lean_box(0));
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v___x_670_);
v_val_673_ = lean_ctor_get(v_a_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_a_672_, 1);
v___x_674_ = lean_box(0);
v___x_675_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__2(v_goal_624_, v_val_673_, v___x_674_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_List_reverse___redArg(v_a_676_);
v_a_665_ = v___x_677_;
goto v___jp_664_;
}
else
{
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_675_, 1);
v_a_665_ = v_a_678_;
goto v___jp_664_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_del_object(v___x_662_);
lean_dec(v_a_660_);
v_a_679_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_675_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v_a_672_);
lean_del_object(v___x_662_);
lean_dec(v_a_660_);
lean_dec_ref(v_goal_624_);
v___x_687_ = l_Lean_MVarId_getType(v___x_670_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1, &l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___closed__1);
v___x_690_ = l_Lean_indentExpr(v_a_688_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v___x_691_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_692_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_687_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_687_);
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
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v___x_670_);
lean_del_object(v___x_662_);
lean_dec(v_a_660_);
lean_dec_ref(v_goal_624_);
v_a_701_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_671_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_671_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_660_);
lean_ctor_set(v___x_666_, 1, v_a_665_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_666_);
v___x_668_ = v___x_662_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_goal_624_);
v_a_710_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_659_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_659_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_goal_624_);
v_a_718_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_656_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_656_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v_goal_624_);
lean_dec_ref(v_le_623_);
lean_dec_ref(v_pre_620_);
v_a_726_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_652_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_652_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v_goal_624_);
lean_dec_ref(v_le_623_);
lean_dec_ref(v_pre_620_);
v_a_734_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_650_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_650_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_636_);
lean_dec_ref(v_goal_624_);
lean_dec_ref(v_le_623_);
lean_dec_ref(v_pre_620_);
v_a_742_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_643_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_643_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_goal_624_);
lean_dec_ref(v_le_623_);
lean_dec_ref(v_mkOpApp_621_);
lean_dec_ref(v_pre_620_);
v_a_750_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_635_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_635_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed(lean_object* v_frame_758_, lean_object* v_pre_759_, lean_object* v_mkOpApp_760_, lean_object* v_excessArgs_761_, lean_object* v_le_762_, lean_object* v_goal_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0(v_frame_758_, v_pre_759_, v_mkOpApp_760_, v_excessArgs_761_, v_le_762_, v_goal_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v_excessArgs_761_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(lean_object* v_i_775_, lean_object* v_frame_776_){
_start:
{
lean_object* v_unframedApp_777_; lean_object* v_pre_778_; lean_object* v_le_779_; lean_object* v_mkOpApp_780_; lean_object* v_excessArgs_781_; lean_object* v___f_782_; lean_object* v___x_783_; 
v_unframedApp_777_ = lean_ctor_get(v_i_775_, 2);
lean_inc_ref(v_unframedApp_777_);
v_pre_778_ = lean_ctor_get(v_i_775_, 0);
lean_inc_ref(v_pre_778_);
v_le_779_ = lean_ctor_get(v_i_775_, 1);
lean_inc_ref(v_le_779_);
v_mkOpApp_780_ = lean_ctor_get(v_i_775_, 5);
lean_inc_ref(v_mkOpApp_780_);
lean_dec_ref(v_i_775_);
v_excessArgs_781_ = lean_ctor_get(v_unframedApp_777_, 3);
lean_inc_ref_n(v_excessArgs_781_, 2);
lean_dec_ref(v_unframedApp_777_);
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame___lam__0___boxed), 16, 5);
lean_closure_set(v___f_782_, 0, v_frame_776_);
lean_closure_set(v___f_782_, 1, v_pre_778_);
lean_closure_set(v___f_782_, 2, v_mkOpApp_780_);
lean_closure_set(v___f_782_, 3, v_excessArgs_781_);
lean_closure_set(v___f_782_, 4, v_le_779_);
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v_excessArgs_781_);
lean_ctor_set(v___x_783_, 1, v___f_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(lean_object* v_mvarId_784_, lean_object* v_val_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___redArg(v_mvarId_784_, v_val_785_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0___boxed(lean_object* v_mvarId_797_, lean_object* v_val_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0(v_mvarId_797_, v_val_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(lean_object* v_00_u03b1_810_, lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___redArg(v_msg_811_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3___boxed(lean_object* v_00_u03b1_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__3(v_00_u03b1_823_, v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0(lean_object* v_00_u03b2_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0___redArg(v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(lean_object* v_f_841_, lean_object* v_a_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___redArg(v_f_841_, v_a_842_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4___boxed(lean_object* v_f_854_, lean_object* v_a_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__1_spec__2_spec__4(v_f_854_, v_a_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, size_t v_x_869_, size_t v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___redArg(v_x_868_, v_x_869_, v_x_870_, v_x_871_, v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_33843__boxed_880_; size_t v_x_33844__boxed_881_; lean_object* v_res_882_; 
v_x_33843__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_x_33844__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1(v_00_u03b2_874_, v_x_875_, v_x_33843__boxed_880_, v_x_33844__boxed_881_, v_x_878_, v_x_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_883_, lean_object* v_n_884_, lean_object* v_k_885_, lean_object* v_v_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6___redArg(v_n_884_, v_k_885_, v_v_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(lean_object* v_00_u03b2_888_, size_t v_depth_889_, lean_object* v_keys_890_, lean_object* v_vals_891_, lean_object* v_heq_892_, lean_object* v_i_893_, lean_object* v_entries_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___redArg(v_depth_889_, v_keys_890_, v_vals_891_, v_i_893_, v_entries_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7___boxed(lean_object* v_00_u03b2_896_, lean_object* v_depth_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_heq_900_, lean_object* v_i_901_, lean_object* v_entries_902_){
_start:
{
size_t v_depth_boxed_903_; lean_object* v_res_904_; 
v_depth_boxed_903_ = lean_unbox_usize(v_depth_897_);
lean_dec(v_depth_897_);
v_res_904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__7(v_00_u03b2_896_, v_depth_boxed_903_, v_keys_898_, v_vals_899_, v_heq_900_, v_i_901_, v_entries_902_);
lean_dec_ref(v_vals_899_);
lean_dec_ref(v_keys_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_x_906_, v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(lean_object* v_i_911_){
_start:
{
lean_object* v_providedFrame_x3f_913_; 
v_providedFrame_x3f_913_ = lean_ctor_get(v_i_911_, 3);
lean_inc(v_providedFrame_x3f_913_);
if (lean_obj_tag(v_providedFrame_x3f_913_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_val_914_ = lean_ctor_get(v_providedFrame_x3f_913_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_providedFrame_x3f_913_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_providedFrame_x3f_913_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_val_914_);
lean_dec(v_providedFrame_x3f_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = l_Lean_Elab_Tactic_VCGen_FrameDecision_ofFrame(v_i_911_, v_val_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 0);
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_providedFrame_x3f_913_);
lean_dec_ref(v_i_911_);
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg___boxed(lean_object* v_i_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(lean_object* v_i_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___redArg(v_i_928_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed(lean_object* v_i_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc(v_i_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(lean_object* v_info_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_966_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_959_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_unsigned_to_nat(2u);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
v___x_971_ = lean_array_push(v___x_970_, v___x_967_);
v___x_972_ = lean_array_push(v___x_971_, v___x_968_);
v___x_973_ = l_Lean_Meta_mkAppOptM(v___x_965_, v___x_972_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___boxed(lean_object* v_info_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp(v_info_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_info_974_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(lean_object* v_info_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Lean_Elab_Tactic_VCGen_WPApp_Pred(v_info_981_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0___boxed(lean_object* v_info_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Elab_Tactic_VCGen_meetFrameProc___lam__0(v_info_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_info_989_);
return v_res_995_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2(void){
_start:
{
lean_object* v___x_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_998_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_defaultFrameInferenceProc___boxed), 11, 0);
v___f_999_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__0));
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__1));
v___x_1001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProc_0__Lean_Elab_Tactic_VCGen_meetOp___closed__3));
v___x_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_ctor_set(v___x_1002_, 2, v___x_1000_);
lean_ctor_set(v___x_1002_, 3, v___f_999_);
lean_ctor_set(v___x_1002_, 4, v___x_998_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2, &l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_meetFrameProc___closed__2);
return v___x_1003_;
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
