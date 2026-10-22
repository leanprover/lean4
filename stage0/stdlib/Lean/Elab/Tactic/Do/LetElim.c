// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: public import Lean.Meta.Tactic.Simp import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isOfNatNatLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfScientificLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isCharLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses_default;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Uses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_FVarUses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_addMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_addMData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_addMData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "BVar index out of bounds: "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_22_){
_start:
{
lean_inc(v_zero_22_);
return v_zero_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_23_);
lean_dec(v_zero_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_zero_28_){
_start:
{
lean_inc(v_zero_28_);
return v_zero_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_zero_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_zero_32_);
lean_dec(v_zero_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_35_){
_start:
{
lean_inc(v_one_35_);
return v_one_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_36_);
lean_dec(v_one_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_one_41_){
_start:
{
lean_inc(v_one_41_);
return v_one_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_one_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_one_45_);
lean_dec(v_one_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_48_){
_start:
{
lean_inc(v_many_48_);
return v_many_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_49_);
lean_dec(v_many_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_many_54_){
_start:
{
lean_inc(v_many_54_);
return v_many_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_many_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_many_58_);
lean_dec(v_many_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_61_, uint8_t v_y_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_63_ = lean_box(v_x_61_);
v___x_64_ = lean_obj_tag_nat(v___x_63_);
lean_dec(v___x_63_);
v___x_65_ = lean_box(v_y_62_);
v___x_66_ = lean_obj_tag_nat(v___x_65_);
lean_dec(v___x_65_);
v___x_67_ = lean_nat_dec_eq(v___x_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v_x_24__boxed_70_; uint8_t v_y_25__boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_x_24__boxed_70_ = lean_unbox(v_x_68_);
v_y_25__boxed_71_ = lean_unbox(v_y_69_);
v_res_72_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_24__boxed_70_, v_y_25__boxed_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_76_, uint8_t v_y_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_78_ = lean_box(v_x_76_);
v___x_79_ = lean_obj_tag_nat(v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = lean_box(v_y_77_);
v___x_81_ = lean_obj_tag_nat(v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = lean_nat_dec_lt(v___x_79_, v___x_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = lean_nat_dec_eq(v___x_79_, v___x_81_);
if (v___x_83_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = 2;
return v___x_84_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_87_, lean_object* v_y_88_){
_start:
{
uint8_t v_x_33__boxed_89_; uint8_t v_y_34__boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_x_33__boxed_89_ = lean_unbox(v_x_87_);
v_y_34__boxed_90_ = lean_unbox(v_y_88_);
v_res_91_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_33__boxed_89_, v_y_34__boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_97_, uint8_t v_x_98_){
_start:
{
if (v_x_97_ == 0)
{
return v_x_98_;
}
else
{
if (v_x_98_ == 0)
{
return v_x_97_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 2;
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_x_18__boxed_102_; uint8_t v_x_19__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_x_18__boxed_102_ = lean_unbox(v_x_100_);
v_x_19__boxed_103_ = lean_unbox(v_x_101_);
v_res_104_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_18__boxed_102_, v_x_19__boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_106_){
_start:
{
switch(v_x_106_)
{
case 0:
{
lean_object* v___x_107_; 
v___x_107_ = lean_unsigned_to_nat(0u);
return v___x_107_;
}
case 1:
{
lean_object* v___x_108_; 
v___x_108_ = lean_unsigned_to_nat(1u);
return v___x_108_;
}
default: 
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(2u);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_x_34__boxed_111_; lean_object* v_res_112_; 
v_x_34__boxed_111_ = lean_unbox(v_x_110_);
v_res_112_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_111_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_nat_dec_eq(v_x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_dec_eq(v_x_113_, v___x_116_);
if (v___x_117_ == 0)
{
uint8_t v___x_118_; 
v___x_118_ = 2;
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 1;
return v___x_119_;
}
}
else
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_121_);
lean_dec(v_x_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
return v_x_126_;
}
else
{
lean_object* v_key_128_; lean_object* v_value_129_; lean_object* v_tail_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_153_; 
v_key_128_ = lean_ctor_get(v_x_127_, 0);
v_value_129_ = lean_ctor_get(v_x_127_, 1);
v_tail_130_ = lean_ctor_get(v_x_127_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_153_ == 0)
{
v___x_132_ = v_x_127_;
v_isShared_133_ = v_isSharedCheck_153_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_tail_130_);
lean_inc(v_value_129_);
lean_inc(v_key_128_);
lean_dec(v_x_127_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_153_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_134_ = lean_array_get_size(v_x_126_);
v___x_135_ = l_Lean_instHashableFVarId_hash(v_key_128_);
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___x_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___x_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_134_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v___x_147_ = lean_array_uget_borrowed(v_x_126_, v___x_146_);
lean_inc(v___x_147_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 2, v___x_147_);
v___x_149_ = v___x_132_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_key_128_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_value_129_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v___x_147_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_array_uset(v_x_126_, v___x_146_, v___x_149_);
v_x_126_ = v___x_150_;
v_x_127_ = v_tail_130_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_154_, lean_object* v_source_155_, lean_object* v_target_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_array_get_size(v_source_155_);
v___x_158_ = lean_nat_dec_lt(v_i_154_, v___x_157_);
if (v___x_158_ == 0)
{
lean_dec_ref(v_source_155_);
lean_dec(v_i_154_);
return v_target_156_;
}
else
{
lean_object* v_es_159_; lean_object* v___x_160_; lean_object* v_source_161_; lean_object* v_target_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_es_159_ = lean_array_fget(v_source_155_, v_i_154_);
v___x_160_ = lean_box(0);
v_source_161_ = lean_array_fset(v_source_155_, v_i_154_, v___x_160_);
v_target_162_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_156_, v_es_159_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_i_154_, v___x_163_);
lean_dec(v_i_154_);
v_i_154_ = v___x_164_;
v_source_155_ = v_source_161_;
v_target_156_ = v_target_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_nbuckets_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_167_ = lean_array_get_size(v_data_166_);
v___x_168_ = lean_unsigned_to_nat(2u);
v_nbuckets_169_ = lean_nat_mul(v___x_167_, v___x_168_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_box(0);
v___x_172_ = lean_mk_array(v_nbuckets_169_, v___x_171_);
v___x_173_ = lean_array_propagate_mark(v_data_166_, v___x_172_);
v___x_174_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_170_, v_data_166_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_175_, lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 0;
return v___x_177_;
}
else
{
lean_object* v_key_178_; lean_object* v_tail_179_; uint8_t v___x_180_; 
v_key_178_ = lean_ctor_get(v_x_176_, 0);
v_tail_179_ = lean_ctor_get(v_x_176_, 2);
v___x_180_ = l_Lean_instBEqFVarId_beq(v_key_178_, v_a_175_);
if (v___x_180_ == 0)
{
v_x_176_ = v_tail_179_;
goto _start;
}
else
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_182_, lean_object* v_x_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_182_, v_x_183_);
lean_dec(v_x_183_);
lean_dec(v_a_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_box(v_x3_186_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_val_190_ = lean_ctor_get(v_x_187_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v_x_187_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v_x_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_194_ = lean_unbox(v_val_190_);
lean_dec(v_val_190_);
v___x_195_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_186_, v___x_194_);
v___x_196_ = lean_box(v___x_195_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_196_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_x3_855__boxed_203_; lean_object* v_res_204_; 
v_x3_855__boxed_203_ = lean_unbox(v_x3_201_);
v_res_204_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_855__boxed_203_, v_x_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_205_, lean_object* v_a_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_val_210_; lean_object* v___x_211_; 
v___x_208_ = lean_box(0);
v___x_209_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_205_, v___x_208_);
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec(v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_211_, 0, v_a_206_);
lean_ctor_set(v___x_211_, 1, v_val_210_);
lean_ctor_set(v___x_211_, 2, v_x_207_);
return v___x_211_;
}
else
{
lean_object* v_key_212_; lean_object* v_value_213_; lean_object* v_tail_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_229_; 
v_key_212_ = lean_ctor_get(v_x_207_, 0);
v_value_213_ = lean_ctor_get(v_x_207_, 1);
v_tail_214_ = lean_ctor_get(v_x_207_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_207_);
if (v_isSharedCheck_229_ == 0)
{
v___x_216_ = v_x_207_;
v_isShared_217_ = v_isSharedCheck_229_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_tail_214_);
lean_inc(v_value_213_);
lean_inc(v_key_212_);
lean_dec(v_x_207_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_229_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_instBEqFVarId_beq(v_key_212_, v_a_206_);
if (v___x_218_ == 0)
{
lean_object* v_tail_219_; lean_object* v___x_221_; 
v_tail_219_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_205_, v_a_206_, v_tail_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 2, v_tail_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_key_212_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_value_213_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_tail_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_val_225_; lean_object* v___x_227_; 
lean_dec(v_key_212_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_value_213_);
v___x_224_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_205_, v___x_223_);
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec(v___x_224_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v_val_225_);
lean_ctor_set(v___x_216_, 0, v_a_206_);
v___x_227_ = v___x_216_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_206_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_val_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_tail_214_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_230_, lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_x3_887__boxed_233_; lean_object* v_res_234_; 
v_x3_887__boxed_233_ = lean_unbox(v_x3_230_);
v_res_234_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_887__boxed_233_, v_a_231_, v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_235_, lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_size_238_; lean_object* v_buckets_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_288_; 
v_size_238_ = lean_ctor_get(v_m_236_, 0);
v_buckets_239_ = lean_ctor_get(v_m_236_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_m_236_);
if (v_isSharedCheck_288_ == 0)
{
v___x_241_ = v_m_236_;
v_isShared_242_ = v_isSharedCheck_288_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_buckets_239_);
lean_inc(v_size_238_);
lean_dec(v_m_236_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_288_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v_bkt_256_; uint8_t v___x_257_; 
v___x_243_ = lean_array_get_size(v_buckets_239_);
v___x_244_ = l_Lean_instHashableFVarId_hash(v_a_237_);
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___x_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___x_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v_bkt_256_ = lean_array_uget_borrowed(v_buckets_239_, v___x_255_);
v___x_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_237_, v_bkt_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v_size_x27_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_buckets_x27_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v_size_x27_259_ = lean_nat_add(v_size_238_, v___x_258_);
lean_dec(v_size_238_);
v___x_260_ = lean_box(v_x3_235_);
lean_inc(v_bkt_256_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v_a_237_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
lean_ctor_set(v___x_261_, 2, v_bkt_256_);
v_buckets_x27_262_ = lean_array_uset(v_buckets_239_, v___x_255_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(4u);
v___x_264_ = lean_nat_mul(v_size_x27_259_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(3u);
v___x_266_ = lean_nat_div(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_array_get_size(v_buckets_x27_262_);
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
if (v___x_268_ == 0)
{
lean_object* v_val_269_; lean_object* v___x_271_; 
v_val_269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_262_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_val_269_);
lean_ctor_set(v___x_241_, 0, v_size_x27_259_);
v___x_271_ = v___x_241_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_val_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v___x_274_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_buckets_x27_262_);
lean_ctor_set(v___x_241_, 0, v_size_x27_259_);
v___x_274_ = v___x_241_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_size_x27_259_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_buckets_x27_262_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v___x_276_; lean_object* v_buckets_x27_277_; lean_object* v_bkt_x27_278_; lean_object* v___y_280_; uint8_t v___x_285_; 
lean_inc(v_bkt_256_);
v___x_276_ = lean_box(0);
v_buckets_x27_277_ = lean_array_uset(v_buckets_239_, v___x_255_, v___x_276_);
lean_inc(v_a_237_);
v_bkt_x27_278_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_235_, v_a_237_, v_bkt_256_);
v___x_285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_237_, v_bkt_x27_278_);
lean_dec(v_a_237_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_sub(v_size_238_, v___x_286_);
lean_dec(v_size_238_);
v___y_280_ = v___x_287_;
goto v___jp_279_;
}
else
{
v___y_280_ = v_size_238_;
goto v___jp_279_;
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_array_uset(v_buckets_x27_277_, v___x_255_, v_bkt_x27_278_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_281_);
lean_ctor_set(v___x_241_, 0, v___y_280_);
v___x_283_ = v___x_241_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___y_280_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_289_, lean_object* v_m_290_, lean_object* v_a_291_){
_start:
{
uint8_t v_x3_935__boxed_292_; lean_object* v_res_293_; 
v_x3_935__boxed_292_ = lean_unbox(v_x3_289_);
v_res_293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_935__boxed_292_, v_m_290_, v_a_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
return v_x_294_;
}
else
{
lean_object* v_key_296_; lean_object* v_value_297_; lean_object* v_tail_298_; uint8_t v___x_299_; lean_object* v___x_300_; 
v_key_296_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_key_296_);
v_value_297_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_value_297_);
v_tail_298_ = lean_ctor_get(v_x_295_, 2);
lean_inc(v_tail_298_);
lean_dec_ref_known(v_x_295_, 3);
v___x_299_ = lean_unbox(v_value_297_);
lean_dec(v_value_297_);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_299_, v_x_294_, v_key_296_);
v_x_294_ = v___x_300_;
v_x_295_ = v_tail_298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_302_, size_t v_i_303_, size_t v_stop_304_, lean_object* v_b_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; size_t v___x_309_; size_t v___x_310_; 
v___x_307_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
lean_inc(v___x_307_);
v___x_308_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_305_, v___x_307_);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_add(v_i_303_, v___x_309_);
v_i_303_ = v___x_310_;
v_b_305_ = v___x_308_;
goto _start;
}
else
{
return v_b_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_stop_314_, lean_object* v_b_315_){
_start:
{
size_t v_i_boxed_316_; size_t v_stop_boxed_317_; lean_object* v_res_318_; 
v_i_boxed_316_ = lean_unbox_usize(v_i_313_);
lean_dec(v_i_313_);
v_stop_boxed_317_ = lean_unbox_usize(v_stop_314_);
lean_dec(v_stop_314_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_312_, v_i_boxed_316_, v_stop_boxed_317_, v_b_315_);
lean_dec_ref(v_as_312_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
lean_object* v_buckets_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_buckets_321_ = lean_ctor_get(v_a_319_, 1);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_array_get_size(v_buckets_321_);
v___x_324_ = lean_nat_dec_lt(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
return v_b_320_;
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_323_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_321_, v___x_325_, v___x_326_, v_b_320_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_328_, v_b_329_);
lean_dec_ref(v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_335_, lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_335_, v_a_336_, v_x_337_);
lean_dec(v_x_337_);
lean_dec(v_a_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_340_, lean_object* v_data_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_343_, lean_object* v_i_344_, lean_object* v_source_345_, lean_object* v_target_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_344_, v_source_345_, v_target_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_349_, v_x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_tag_nat(v_x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg___boxed(lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(v_x_356_);
lean_dec(v_x_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(lean_object* v_n_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_tag_nat(v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___boxed(lean_object* v_n_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(v_n_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec(v_n_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_364_, lean_object* v_k_365_){
_start:
{
if (lean_obj_tag(v_t_364_) == 0)
{
return v_k_365_;
}
else
{
lean_object* v_uses_366_; lean_object* v___x_367_; 
v_uses_366_ = lean_ctor_get(v_t_364_, 0);
lean_inc_ref(v_uses_366_);
lean_dec_ref_known(v_t_364_, 1);
v___x_367_ = lean_apply_1(v_k_365_, v_uses_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_368_, lean_object* v_motive_369_, lean_object* v_ctorIdx_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_k_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_371_, v_k_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_375_, lean_object* v_motive_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_375_, v_motive_376_, v_ctorIdx_377_, v_t_378_, v_h_379_, v_k_380_);
lean_dec(v_ctorIdx_377_);
lean_dec(v_n_375_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_382_, lean_object* v_none_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_382_, v_none_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_385_, lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_none_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_387_, v_none_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_391_, lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_none_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_391_, v_motive_392_, v_t_393_, v_h_394_, v_none_395_);
lean_dec(v_n_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_397_, lean_object* v_some_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_397_, v_some_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_400_, lean_object* v_motive_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_some_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_402_, v_some_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_406_, lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_some_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_406_, v_motive_407_, v_t_408_, v_h_409_, v_some_410_);
lean_dec(v_n_406_);
return v_res_411_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_437_ = l_Lean_mkAtom(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_442_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_443_ = lean_box(2);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_446_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_447_ = lean_array_push(v___x_446_, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_449_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_450_ = lean_box(2);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_453_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_454_ = lean_array_push(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_457_ = lean_box(2);
v___x_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_461_ = lean_array_push(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_463_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_464_ = lean_box(2);
v___x_465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_462_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_467_, lean_object* v_n_468_, lean_object* v_i_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = lean_nat_sub(v_numBVars_467_, v___x_470_);
v___x_472_ = lean_nat_sub(v___x_471_, v_n_468_);
lean_dec(v___x_471_);
v___x_473_ = lean_nat_dec_eq(v_i_469_, v___x_472_);
lean_dec(v___x_472_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = 1;
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_476_, lean_object* v_n_477_, lean_object* v_i_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_476_, v_n_477_, v_i_478_);
lean_dec(v_i_478_);
lean_dec(v_n_477_);
lean_dec(v_numBVars_476_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_481_, lean_object* v_n_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_numBVars_481_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_483_, 0, v_numBVars_481_);
lean_closure_set(v___f_483_, 1, v_n_482_);
v___x_484_ = l_Array_ofFn___redArg(v_numBVars_481_, v___f_483_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_486_, lean_object* v_n_487_, lean_object* v_x_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_486_, v_n_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_496_;
}
else
{
lean_object* v_uses_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_510_; 
v_uses_497_ = lean_ctor_get(v_x_495_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_510_ == 0)
{
v___x_499_ = v_x_495_;
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_uses_497_);
lean_dec(v_x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_numBVars_494_, v___x_501_);
v___x_503_ = lean_nat_sub(v___x_502_, v___x_501_);
lean_dec(v___x_502_);
v___x_504_ = lean_array_fget(v_uses_497_, v___x_503_);
lean_dec(v___x_503_);
v___x_505_ = lean_array_pop(v_uses_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_505_);
v___x_507_ = v___x_499_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_504_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_511_, v_x_512_);
lean_dec(v_numBVars_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_514_, lean_object* v_bs_515_, lean_object* v_i_516_, lean_object* v_cs_517_){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_as_514_);
v___x_519_ = lean_nat_dec_lt(v_i_516_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_i_516_);
return v_cs_517_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_bs_515_);
v___x_521_ = lean_nat_dec_lt(v_i_516_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v_i_516_);
return v_cs_517_;
}
else
{
lean_object* v_a_522_; lean_object* v_b_523_; uint8_t v___x_524_; uint8_t v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_522_ = lean_array_fget_borrowed(v_as_514_, v_i_516_);
v_b_523_ = lean_array_fget_borrowed(v_bs_515_, v_i_516_);
v___x_524_ = lean_unbox(v_a_522_);
v___x_525_ = lean_unbox(v_b_523_);
v___x_526_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_524_, v___x_525_);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_i_516_, v___x_527_);
lean_dec(v_i_516_);
v___x_529_ = lean_box(v___x_526_);
v___x_530_ = lean_array_push(v_cs_517_, v___x_529_);
v_i_516_ = v___x_528_;
v_cs_517_ = v___x_530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_532_, lean_object* v_bs_533_, lean_object* v_i_534_, lean_object* v_cs_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_532_, v_bs_533_, v_i_534_, v_cs_535_);
lean_dec_ref(v_bs_533_);
lean_dec_ref(v_as_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_539_, lean_object* v_b_540_){
_start:
{
if (lean_obj_tag(v_a_539_) == 0)
{
return v_b_540_;
}
else
{
if (lean_obj_tag(v_b_540_) == 0)
{
lean_object* v_uses_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_uses_541_ = lean_ctor_get(v_a_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v_a_539_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_uses_541_);
lean_dec(v_a_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_uses_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_uses_549_; lean_object* v_uses_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v_uses_549_ = lean_ctor_get(v_a_539_, 0);
lean_inc_ref(v_uses_549_);
lean_dec_ref_known(v_a_539_, 1);
v_uses_550_ = lean_ctor_get(v_b_540_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_b_540_);
if (v_isSharedCheck_560_ == 0)
{
v___x_552_ = v_b_540_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_uses_550_);
lean_dec(v_b_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_556_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_549_, v_uses_550_, v___x_554_, v___x_555_);
lean_dec_ref(v_uses_550_);
lean_dec_ref(v_uses_549_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_556_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_561_, lean_object* v_a_562_, lean_object* v_b_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_562_, v_b_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_565_, lean_object* v_a_566_, lean_object* v_b_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_565_, v_a_566_, v_b_567_);
lean_dec(v_numBVars_565_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_570_, 0, v_numBVars_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_582_; 
v_fst_573_ = lean_ctor_get(v_x_572_, 0);
v_snd_574_ = lean_ctor_get(v_x_572_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_576_ = v_x_572_;
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snd_574_);
lean_inc(v_fst_573_);
lean_dec(v_x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_582_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_apply_1(v_f_571_, v_fst_573_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_574_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_583_, lean_object* v_00_u03b1_u2082_584_, lean_object* v_00_u03b2_585_, lean_object* v_f_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_586_, v_x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_589_, lean_object* v_new_590_, lean_object* v_x_591_){
_start:
{
lean_inc_ref(v_new_590_);
return v_new_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_592_, lean_object* v_new_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_592_, v_new_593_, v_x_594_);
lean_dec_ref(v_x_594_);
lean_dec_ref(v_new_593_);
lean_dec(v_x_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_597_, lean_object* v_e_598_){
_start:
{
if (lean_obj_tag(v_e_598_) == 10)
{
lean_object* v_data_599_; lean_object* v_expr_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_data_599_ = lean_ctor_get(v_e_598_, 0);
lean_inc(v_data_599_);
v_expr_600_ = lean_ctor_get(v_e_598_, 1);
lean_inc_ref(v_expr_600_);
lean_dec_ref_known(v_e_598_, 2);
v___f_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_602_ = l_Lean_KVMap_mergeBy(v___f_601_, v_d_597_, v_data_599_);
lean_dec(v_data_599_);
v___x_603_ = l_Lean_Expr_mdata___override(v___x_602_, v_expr_600_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Expr_mdata___override(v_d_597_, v_e_598_);
return v___x_604_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_605_){
_start:
{
switch(lean_obj_tag(v_e_605_))
{
case 1:
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
case 5:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_605_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_605_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Meta_Simp_isCharLit(v_e_605_);
return v___x_609_;
}
else
{
return v___x_608_;
}
}
else
{
return v___x_607_;
}
}
case 6:
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
case 7:
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
case 8:
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
case 10:
{
lean_object* v_expr_613_; 
v_expr_613_ = lean_ctor_get(v_e_605_, 1);
v_e_605_ = v_expr_613_;
goto _start;
}
case 11:
{
lean_object* v_struct_615_; 
v_struct_615_ = lean_ctor_get(v_e_605_, 2);
v_e_605_ = v_struct_615_;
goto _start;
}
default: 
{
uint8_t v___x_617_; 
v___x_617_ = 1;
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_618_);
lean_dec_ref(v_e_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_val_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v_env_630_; uint8_t v___x_631_; lean_object* v_env_632_; lean_object* v___x_633_; lean_object* v_toCold_634_; lean_object* v_mctx_635_; lean_object* v_lctx_636_; lean_object* v_options_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_629_ = lean_st_ref_get(v___y_627_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc_ref(v_env_630_);
lean_dec(v___x_629_);
v___x_631_ = 0;
v_env_632_ = l_Lean_Environment_setRecordingDeps(v_env_630_, v___x_631_);
v___x_633_ = lean_st_ref_get(v___y_625_);
v_toCold_634_ = lean_ctor_get(v___y_626_, 0);
v_mctx_635_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_mctx_635_);
lean_dec(v___x_633_);
v_lctx_636_ = lean_ctor_get(v___y_624_, 2);
v_options_637_ = lean_ctor_get(v_toCold_634_, 2);
lean_inc_ref(v_options_637_);
lean_inc_ref(v_lctx_636_);
v___x_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_638_, 0, v_env_632_);
lean_ctor_set(v___x_638_, 1, v_mctx_635_);
lean_ctor_set(v___x_638_, 2, v_lctx_636_);
lean_ctor_set(v___x_638_, 3, v_options_637_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_msgData_623_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_ref_654_ = lean_ctor_get(v___y_651_, 2);
v___x_655_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_inc(v_ref_654_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_ref_654_);
lean_ctor_set(v___x_660_, 1, v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 1);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_672_, lean_object* v_expr_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Expr_mdata___override(v_data_672_, v_expr_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_675_, lean_object* v_idx_676_, lean_object* v_struct_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Expr_proj___override(v_typeName_675_, v_idx_676_, v_struct_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_dec(v_b_680_);
lean_dec(v_a_679_);
return v_x_681_;
}
else
{
lean_object* v_key_682_; lean_object* v_value_683_; lean_object* v_tail_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_key_682_ = lean_ctor_get(v_x_681_, 0);
v_value_683_ = lean_ctor_get(v_x_681_, 1);
v_tail_684_ = lean_ctor_get(v_x_681_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v_x_681_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_tail_684_);
lean_inc(v_value_683_);
lean_inc(v_key_682_);
lean_dec(v_x_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_instBEqFVarId_beq(v_key_682_, v_a_679_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_679_, v_b_680_, v_tail_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 2, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_value_683_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v_value_683_);
lean_dec(v_key_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_b_680_);
lean_ctor_set(v___x_686_, 0, v_a_679_);
v___x_694_ = v___x_686_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_679_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_b_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_tail_684_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
lean_object* v_size_700_; lean_object* v_buckets_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_744_; 
v_size_700_ = lean_ctor_get(v_m_697_, 0);
v_buckets_701_ = lean_ctor_get(v_m_697_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_m_697_);
if (v_isSharedCheck_744_ == 0)
{
v___x_703_ = v_m_697_;
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_buckets_701_);
lean_inc(v_size_700_);
lean_dec(v_m_697_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v_fold_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; lean_object* v_bkt_718_; uint8_t v___x_719_; 
v___x_705_ = lean_array_get_size(v_buckets_701_);
v___x_706_ = l_Lean_instHashableFVarId_hash(v_a_698_);
v___x_707_ = 32ULL;
v___x_708_ = lean_uint64_shift_right(v___x_706_, v___x_707_);
v_fold_709_ = lean_uint64_xor(v___x_706_, v___x_708_);
v___x_710_ = 16ULL;
v___x_711_ = lean_uint64_shift_right(v_fold_709_, v___x_710_);
v___x_712_ = lean_uint64_xor(v_fold_709_, v___x_711_);
v___x_713_ = lean_uint64_to_usize(v___x_712_);
v___x_714_ = lean_usize_of_nat(v___x_705_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_sub(v___x_714_, v___x_715_);
v___x_717_ = lean_usize_land(v___x_713_, v___x_716_);
v_bkt_718_ = lean_array_uget_borrowed(v_buckets_701_, v___x_717_);
v___x_719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_698_, v_bkt_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v_size_x27_721_; lean_object* v___x_722_; lean_object* v_buckets_x27_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v_size_x27_721_ = lean_nat_add(v_size_700_, v___x_720_);
lean_dec(v_size_700_);
lean_inc(v_bkt_718_);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v_a_698_);
lean_ctor_set(v___x_722_, 1, v_b_699_);
lean_ctor_set(v___x_722_, 2, v_bkt_718_);
v_buckets_x27_723_ = lean_array_uset(v_buckets_701_, v___x_717_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_nat_mul(v_size_x27_721_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(3u);
v___x_727_ = lean_nat_div(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_array_get_size(v_buckets_x27_723_);
v___x_729_ = lean_nat_dec_le(v___x_727_, v___x_728_);
lean_dec(v___x_727_);
if (v___x_729_ == 0)
{
lean_object* v_val_730_; lean_object* v___x_732_; 
v_val_730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_723_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_val_730_);
lean_ctor_set(v___x_703_, 0, v_size_x27_721_);
v___x_732_ = v___x_703_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_size_x27_721_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_val_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
else
{
lean_object* v___x_735_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_buckets_x27_723_);
lean_ctor_set(v___x_703_, 0, v_size_x27_721_);
v___x_735_ = v___x_703_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_size_x27_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_buckets_x27_723_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v___x_737_; lean_object* v_buckets_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_inc(v_bkt_718_);
v___x_737_ = lean_box(0);
v_buckets_x27_738_ = lean_array_uset(v_buckets_701_, v___x_717_, v___x_737_);
v___x_739_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_698_, v_b_699_, v_bkt_718_);
v___x_740_ = lean_array_uset(v_buckets_x27_738_, v___x_717_, v___x_739_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_740_);
v___x_742_ = v___x_703_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_size_700_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v_ngen_748_; lean_object* v_namePrefix_749_; lean_object* v_idx_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_780_; 
v___x_747_ = lean_st_ref_get(v___y_745_);
v_ngen_748_ = lean_ctor_get(v___x_747_, 2);
lean_inc_ref(v_ngen_748_);
lean_dec(v___x_747_);
v_namePrefix_749_ = lean_ctor_get(v_ngen_748_, 0);
v_idx_750_ = lean_ctor_get(v_ngen_748_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_ngen_748_);
if (v_isSharedCheck_780_ == 0)
{
v___x_752_ = v_ngen_748_;
v_isShared_753_ = v_isSharedCheck_780_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_idx_750_);
lean_inc(v_namePrefix_749_);
lean_dec(v_ngen_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_780_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_r_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_idx_750_);
lean_inc(v_namePrefix_749_);
v_r_754_ = l_Lean_Name_num___override(v_namePrefix_749_, v_idx_750_);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_idx_750_, v___x_755_);
lean_dec(v_idx_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_756_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_namePrefix_749_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_756_);
v___x_758_ = v_reuseFailAlloc_779_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v_nextMacroScope_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_traceState_763_; lean_object* v_cache_764_; lean_object* v_recordedDeps_765_; lean_object* v_messages_766_; lean_object* v_infoState_767_; lean_object* v_snapshotTasks_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v___x_759_ = lean_st_ref_take(v___y_745_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
v_nextMacroScope_761_ = lean_ctor_get(v___x_759_, 1);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_759_, 3);
v_traceState_763_ = lean_ctor_get(v___x_759_, 4);
v_cache_764_ = lean_ctor_get(v___x_759_, 5);
v_recordedDeps_765_ = lean_ctor_get(v___x_759_, 6);
v_messages_766_ = lean_ctor_get(v___x_759_, 7);
v_infoState_767_ = lean_ctor_get(v___x_759_, 8);
v_snapshotTasks_768_ = lean_ctor_get(v___x_759_, 9);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_759_, 2);
lean_dec(v_unused_778_);
v___x_770_ = v___x_759_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snapshotTasks_768_);
lean_inc(v_infoState_767_);
lean_inc(v_messages_766_);
lean_inc(v_recordedDeps_765_);
lean_inc(v_cache_764_);
lean_inc(v_traceState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_nextMacroScope_761_);
lean_inc(v_env_760_);
lean_dec(v___x_759_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 2, v___x_758_);
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_env_760_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextMacroScope_761_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_traceState_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v_cache_764_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_recordedDeps_765_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_messages_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_infoState_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 9, v_snapshotTasks_768_);
v___x_773_ = v_reuseFailAlloc_776_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_st_ref_put(v___y_745_, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_r_754_);
return v___x_775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_781_);
lean_dec(v___y_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v___x_789_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_787_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
return v_x_805_;
}
else
{
lean_object* v_key_806_; lean_object* v_value_807_; lean_object* v_tail_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_817_; 
v_key_806_ = lean_ctor_get(v_x_805_, 0);
v_value_807_ = lean_ctor_get(v_x_805_, 1);
v_tail_808_ = lean_ctor_get(v_x_805_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_817_ == 0)
{
v___x_810_ = v_x_805_;
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_tail_808_);
lean_inc(v_value_807_);
lean_inc(v_key_806_);
lean_dec(v_x_805_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_817_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = l_Lean_instBEqFVarId_beq(v_key_806_, v_a_804_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_804_, v_tail_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 2, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_key_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_value_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_del_object(v___x_810_);
lean_dec(v_value_807_);
lean_dec(v_key_806_);
return v_tail_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_818_, v_x_819_);
lean_dec(v_a_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_size_823_; lean_object* v_buckets_824_; lean_object* v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v_fold_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v_bkt_838_; uint8_t v___x_839_; 
v_size_823_ = lean_ctor_get(v_m_821_, 0);
v_buckets_824_ = lean_ctor_get(v_m_821_, 1);
v___x_825_ = lean_array_get_size(v_buckets_824_);
v___x_826_ = l_Lean_instHashableFVarId_hash(v_a_822_);
v___x_827_ = 32ULL;
v___x_828_ = lean_uint64_shift_right(v___x_826_, v___x_827_);
v_fold_829_ = lean_uint64_xor(v___x_826_, v___x_828_);
v___x_830_ = 16ULL;
v___x_831_ = lean_uint64_shift_right(v_fold_829_, v___x_830_);
v___x_832_ = lean_uint64_xor(v_fold_829_, v___x_831_);
v___x_833_ = lean_uint64_to_usize(v___x_832_);
v___x_834_ = lean_usize_of_nat(v___x_825_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_sub(v___x_834_, v___x_835_);
v___x_837_ = lean_usize_land(v___x_833_, v___x_836_);
v_bkt_838_ = lean_array_uget_borrowed(v_buckets_824_, v___x_837_);
v___x_839_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_822_, v_bkt_838_);
if (v___x_839_ == 0)
{
return v_m_821_;
}
else
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_852_; 
lean_inc(v_bkt_838_);
lean_inc_ref(v_buckets_824_);
lean_inc(v_size_823_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_m_821_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_853_ = lean_ctor_get(v_m_821_, 1);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_m_821_, 0);
lean_dec(v_unused_854_);
v___x_841_ = v_m_821_;
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_m_821_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_buckets_x27_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_843_ = lean_box(0);
v_buckets_x27_844_ = lean_array_uset(v_buckets_824_, v___x_837_, v___x_843_);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_sub(v_size_823_, v___x_845_);
lean_dec(v_size_823_);
v___x_847_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_822_, v_bkt_838_);
v___x_848_ = lean_array_uset(v_buckets_x27_844_, v___x_837_, v___x_847_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_848_);
lean_ctor_set(v___x_841_, 0, v___x_846_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_855_, v_a_856_);
lean_dec(v_a_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_858_, lean_object* v_fallback_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_inc(v_fallback_859_);
return v_fallback_859_;
}
else
{
lean_object* v_key_861_; lean_object* v_value_862_; lean_object* v_tail_863_; uint8_t v___x_864_; 
v_key_861_ = lean_ctor_get(v_x_860_, 0);
v_value_862_ = lean_ctor_get(v_x_860_, 1);
v_tail_863_ = lean_ctor_get(v_x_860_, 2);
v___x_864_ = l_Lean_instBEqFVarId_beq(v_key_861_, v_a_858_);
if (v___x_864_ == 0)
{
v_x_860_ = v_tail_863_;
goto _start;
}
else
{
lean_inc(v_value_862_);
return v_value_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_866_, lean_object* v_fallback_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_866_, v_fallback_867_, v_x_868_);
lean_dec(v_x_868_);
lean_dec(v_fallback_867_);
lean_dec(v_a_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_870_, lean_object* v_a_871_, lean_object* v_fallback_872_){
_start:
{
lean_object* v_buckets_873_; lean_object* v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v_fold_878_; uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_buckets_873_ = lean_ctor_get(v_m_870_, 1);
v___x_874_ = lean_array_get_size(v_buckets_873_);
v___x_875_ = l_Lean_instHashableFVarId_hash(v_a_871_);
v___x_876_ = 32ULL;
v___x_877_ = lean_uint64_shift_right(v___x_875_, v___x_876_);
v_fold_878_ = lean_uint64_xor(v___x_875_, v___x_877_);
v___x_879_ = 16ULL;
v___x_880_ = lean_uint64_shift_right(v_fold_878_, v___x_879_);
v___x_881_ = lean_uint64_xor(v_fold_878_, v___x_880_);
v___x_882_ = lean_uint64_to_usize(v___x_881_);
v___x_883_ = lean_usize_of_nat(v___x_874_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_sub(v___x_883_, v___x_884_);
v___x_886_ = lean_usize_land(v___x_882_, v___x_885_);
v___x_887_ = lean_array_uget_borrowed(v_buckets_873_, v___x_886_);
v___x_888_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_871_, v_fallback_872_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_889_, lean_object* v_a_890_, lean_object* v_fallback_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_889_, v_a_890_, v_fallback_891_);
lean_dec(v_fallback_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_m_889_);
return v_res_892_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
v___x_898_ = lean_unsigned_to_nat(16u);
v___x_899_ = lean_mk_array(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_912_, lean_object* v_subst_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
switch(lean_obj_tag(v_e_912_))
{
case 0:
{
lean_object* v_deBruijnIndex_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_deBruijnIndex_919_ = lean_ctor_get(v_e_912_, 0);
v___x_920_ = lean_array_get_size(v_subst_913_);
v___x_921_ = lean_nat_dec_lt(v_deBruijnIndex_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_inc(v_deBruijnIndex_919_);
lean_dec_ref_known(v_e_912_, 1);
lean_dec_ref(v_subst_913_);
v___x_922_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_923_ = l_Nat_reprFast(v_deBruijnIndex_919_);
v___x_924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = l_Lean_MessageData_ofFormat(v___x_924_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_922_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Nat_reprFast(v___x_920_);
v___x_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
v___x_931_ = l_Lean_MessageData_ofFormat(v___x_930_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_932_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_sub(v___x_920_, v___x_934_);
v___x_936_ = lean_nat_sub(v___x_935_, v_deBruijnIndex_919_);
lean_dec(v___x_935_);
v___x_937_ = lean_array_fget(v_subst_913_, v___x_936_);
lean_dec(v___x_936_);
lean_dec_ref(v_subst_913_);
v___x_938_ = 1;
v___x_939_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_940_ = lean_box(v___x_938_);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_939_, v___x_937_, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_e_912_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
case 1:
{
lean_object* v_fvarId_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v_subst_913_);
v_fvarId_944_ = lean_ctor_get(v_e_912_, 0);
v___x_945_ = 1;
v___x_946_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_947_ = lean_box(v___x_945_);
lean_inc(v_fvarId_944_);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_946_, v_fvarId_944_, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_e_912_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
case 5:
{
lean_object* v_fn_951_; lean_object* v_arg_952_; lean_object* v___x_953_; 
v_fn_951_ = lean_ctor_get(v_e_912_, 0);
lean_inc_ref(v_fn_951_);
v_arg_952_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_arg_952_);
lean_dec_ref_known(v_e_912_, 2);
lean_inc_ref(v_subst_913_);
v___x_953_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_951_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_fst_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_fst_955_);
v_snd_956_ = lean_ctor_get(v_a_954_, 1);
lean_inc(v_snd_956_);
lean_dec(v_a_954_);
v___x_957_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_952_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_976_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_976_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_976_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_976_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_975_; 
v_fst_962_ = lean_ctor_get(v_a_958_, 0);
v_snd_963_ = lean_ctor_get(v_a_958_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_975_ == 0)
{
v___x_965_ = v_a_958_;
v_isShared_966_ = v_isSharedCheck_975_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_snd_963_);
lean_inc(v_fst_962_);
lean_dec(v_a_958_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_975_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = l_Lean_Expr_app___override(v_fst_955_, v_fst_962_);
v___x_968_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_956_, v_snd_963_);
lean_dec(v_snd_956_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v___x_968_);
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_970_);
v___x_972_ = v___x_960_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_dec(v_snd_956_);
lean_dec(v_fst_955_);
return v___x_957_;
}
}
else
{
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_subst_913_);
return v___x_953_;
}
}
case 6:
{
lean_object* v_binderName_977_; lean_object* v_binderType_978_; lean_object* v_body_979_; uint8_t v_binderInfo_980_; lean_object* v___x_981_; 
v_binderName_977_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_binderName_977_);
v_binderType_978_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_binderType_978_);
v_body_979_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_body_979_);
v_binderInfo_980_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_912_, 3);
v___x_981_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
lean_inc_ref(v_subst_913_);
v___x_983_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_978_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_fst_985_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_snd_986_);
lean_dec(v_a_984_);
lean_inc(v_a_982_);
v___x_987_ = lean_array_push(v_subst_913_, v_a_982_);
v___x_988_ = l_Lean_Elab_Tactic_Do_countUses(v_body_979_, v___x_987_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1008_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1008_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1007_; 
v_fst_993_ = lean_ctor_get(v_a_989_, 0);
v_snd_994_ = lean_ctor_get(v_a_989_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_a_989_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_996_ = v_a_989_;
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v_a_989_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1007_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_998_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_986_, v_snd_994_);
lean_dec(v_snd_986_);
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_998_, v_a_982_);
lean_dec(v_a_982_);
v___x_1000_ = l_Lean_Expr_lam___override(v_binderName_977_, v_fst_985_, v_fst_993_, v_binderInfo_980_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_999_);
lean_ctor_set(v___x_996_, 0, v___x_1000_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_999_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1002_);
v___x_1004_ = v___x_991_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
lean_dec(v_a_982_);
lean_dec(v_binderName_977_);
return v___x_988_;
}
}
else
{
lean_dec(v_a_982_);
lean_dec_ref(v_body_979_);
lean_dec(v_binderName_977_);
lean_dec_ref(v_subst_913_);
return v___x_983_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_body_979_);
lean_dec_ref(v_binderType_978_);
lean_dec(v_binderName_977_);
lean_dec_ref(v_subst_913_);
v_a_1009_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_981_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_981_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1017_; lean_object* v_binderType_1018_; lean_object* v_body_1019_; uint8_t v_binderInfo_1020_; lean_object* v___x_1021_; 
v_binderName_1017_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_binderName_1017_);
v_binderType_1018_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_binderType_1018_);
v_body_1019_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_body_1019_);
v_binderInfo_1020_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_912_, 3);
v___x_1021_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
lean_inc_ref(v_subst_913_);
v___x_1023_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1018_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_fst_1025_ = lean_ctor_get(v_a_1024_, 0);
lean_inc(v_fst_1025_);
v_snd_1026_ = lean_ctor_get(v_a_1024_, 1);
lean_inc(v_snd_1026_);
lean_dec(v_a_1024_);
lean_inc(v_a_1022_);
v___x_1027_ = lean_array_push(v_subst_913_, v_a_1022_);
v___x_1028_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1019_, v___x_1027_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1048_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1047_; 
v_fst_1033_ = lean_ctor_get(v_a_1029_, 0);
v_snd_1034_ = lean_ctor_get(v_a_1029_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1036_ = v_a_1029_;
v_isShared_1037_ = v_isSharedCheck_1047_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_snd_1034_);
lean_inc(v_fst_1033_);
lean_dec(v_a_1029_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1047_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1038_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1026_, v_snd_1034_);
lean_dec(v_snd_1026_);
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1038_, v_a_1022_);
lean_dec(v_a_1022_);
v___x_1040_ = l_Lean_Expr_forallE___override(v_binderName_1017_, v_fst_1025_, v_fst_1033_, v_binderInfo_1020_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1042_ = v___x_1036_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1039_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1042_);
v___x_1044_ = v___x_1031_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
else
{
lean_dec(v_snd_1026_);
lean_dec(v_fst_1025_);
lean_dec(v_a_1022_);
lean_dec(v_binderName_1017_);
return v___x_1028_;
}
}
else
{
lean_dec(v_a_1022_);
lean_dec_ref(v_body_1019_);
lean_dec(v_binderName_1017_);
lean_dec_ref(v_subst_913_);
return v___x_1023_;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_body_1019_);
lean_dec_ref(v_binderType_1018_);
lean_dec(v_binderName_1017_);
lean_dec_ref(v_subst_913_);
v_a_1049_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1021_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1021_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
case 8:
{
lean_object* v_declName_1057_; lean_object* v_type_1058_; lean_object* v_value_1059_; lean_object* v_body_1060_; uint8_t v_nondep_1061_; lean_object* v___x_1062_; 
v_declName_1057_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_declName_1057_);
v_type_1058_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_type_1058_);
v_value_1059_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_value_1059_);
v_body_1060_ = lean_ctor_get(v_e_912_, 3);
lean_inc_ref(v_body_1060_);
v_nondep_1061_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_912_, 4);
v___x_1062_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_n(v_a_1063_, 2);
lean_dec_ref_known(v___x_1062_, 1);
lean_inc_ref(v_subst_913_);
v___x_1064_ = lean_array_push(v_subst_913_, v_a_1063_);
v___x_1065_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1060_, v___x_1064_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1108_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1108_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1108_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v_fst_1070_; lean_object* v_snd_1071_; lean_object* v___x_1073_; 
v_fst_1070_ = lean_ctor_get(v_a_1066_, 0);
lean_inc(v_fst_1070_);
v_snd_1071_ = lean_ctor_get(v_a_1066_, 1);
lean_inc(v_snd_1071_);
lean_dec(v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 1);
lean_ctor_set(v___x_1068_, 0, v_value_1059_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_value_1059_);
v___x_1073_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1063_, v_type_1058_, v___x_1073_, v_snd_1071_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_1063_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1098_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1098_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1098_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_snd_1079_; lean_object* v_fst_1080_; 
v_snd_1079_ = lean_ctor_get(v_a_1075_, 1);
lean_inc(v_snd_1079_);
v_fst_1080_ = lean_ctor_get(v_snd_1079_, 0);
lean_inc(v_fst_1080_);
if (lean_obj_tag(v_fst_1080_) == 1)
{
lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1094_; 
v_fst_1081_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_fst_1081_);
lean_dec(v_a_1075_);
v_snd_1082_ = lean_ctor_get(v_snd_1079_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_snd_1079_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_snd_1079_, 0);
lean_dec(v_unused_1095_);
v___x_1084_ = v_snd_1079_;
v_isShared_1085_ = v_isSharedCheck_1094_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_snd_1082_);
lean_dec(v_snd_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1094_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_val_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_val_1086_ = lean_ctor_get(v_fst_1080_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_fst_1080_, 1);
v___x_1087_ = l_Lean_Expr_letE___override(v_declName_1057_, v_fst_1081_, v_val_1086_, v_fst_1070_, v_nondep_1061_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1087_);
v___x_1089_ = v___x_1084_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_snd_1082_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1089_);
v___x_1091_ = v___x_1077_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v_fst_1080_);
lean_dec(v_snd_1079_);
lean_del_object(v___x_1077_);
lean_dec(v_a_1075_);
lean_dec(v_fst_1070_);
lean_dec(v_declName_1057_);
v___x_1096_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1097_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1096_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_fst_1070_);
lean_dec(v_declName_1057_);
v_a_1099_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1074_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1074_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1063_);
lean_dec_ref(v_value_1059_);
lean_dec_ref(v_type_1058_);
lean_dec(v_declName_1057_);
lean_dec_ref(v_subst_913_);
return v___x_1065_;
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_body_1060_);
lean_dec_ref(v_value_1059_);
lean_dec_ref(v_type_1058_);
lean_dec(v_declName_1057_);
lean_dec_ref(v_subst_913_);
v_a_1109_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1062_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1062_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
case 10:
{
lean_object* v_data_1117_; lean_object* v_expr_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_data_1117_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_data_1117_);
v_expr_1118_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_expr_1118_);
lean_dec_ref_known(v_e_912_, 2);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1119_, 0, v_data_1117_);
v___x_1120_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1118_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1119_, v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_dec_ref(v___f_1119_);
return v___x_1120_;
}
}
case 11:
{
lean_object* v_typeName_1130_; lean_object* v_idx_1131_; lean_object* v_struct_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v_typeName_1130_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_typeName_1130_);
v_idx_1131_ = lean_ctor_get(v_e_912_, 1);
lean_inc(v_idx_1131_);
v_struct_1132_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_struct_1132_);
lean_dec_ref_known(v_e_912_, 3);
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1133_, 0, v_typeName_1130_);
lean_closure_set(v___f_1133_, 1, v_idx_1131_);
v___x_1134_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1132_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1133_, v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_dec_ref(v___f_1133_);
return v___x_1134_;
}
}
default: 
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_subst_913_);
v___x_1144_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_e_912_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1147_, lean_object* v_ty_1148_, lean_object* v_val_x3f_1149_, lean_object* v_bodyUses_1150_, lean_object* v_subst_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___f_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0));
lean_inc_ref(v_subst_1151_);
v___x_1158_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1148_, v_subst_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1213_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1213_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1213_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1212_; 
v_fst_1163_ = lean_ctor_get(v_a_1159_, 0);
v_snd_1164_ = lean_ctor_get(v_a_1159_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_a_1159_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1166_ = v_a_1159_;
v_isShared_1167_ = v_isSharedCheck_1212_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_snd_1164_);
lean_inc(v_fst_1163_);
lean_dec(v_a_1159_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1212_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; 
if (lean_obj_tag(v_val_x3f_1149_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_subst_1151_);
v___x_1197_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v_fst_1186_ = v_val_x3f_1149_;
v_snd_1187_ = v___x_1197_;
goto v___jp_1185_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1199_; 
v_val_1198_ = lean_ctor_get(v_val_x3f_1149_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_val_x3f_1149_, 1);
v___x_1199_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1198_, v_subst_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v_fst_1202_; lean_object* v_snd_1203_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1157_, v_a_1200_);
v_fst_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_fst_1202_);
v_snd_1203_ = lean_ctor_get(v___x_1201_, 1);
lean_inc(v_snd_1203_);
lean_dec_ref(v___x_1201_);
v_fst_1186_ = v_fst_1202_;
v_snd_1187_ = v_snd_1203_;
goto v___jp_1185_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_del_object(v___x_1166_);
lean_dec(v_snd_1164_);
lean_dec(v_fst_1163_);
lean_del_object(v___x_1161_);
lean_dec_ref(v_bodyUses_1150_);
v_a_1204_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1199_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1171_, v_fvarId_1147_);
v___x_1173_ = lean_box(0);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1175_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1170_);
v___x_1176_ = l_Lean_KVMap_setNat(v___x_1173_, v___x_1174_, v___x_1175_);
v___x_1177_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1176_, v_fst_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1172_);
lean_ctor_set(v___x_1166_, 0, v___y_1169_);
v___x_1179_ = v___x_1166_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___y_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1172_);
v___x_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1177_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1180_);
v___x_1182_ = v___x_1161_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
v___jp_1185_:
{
uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1188_ = 0;
v___x_1189_ = lean_box(v___x_1188_);
v___x_1190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1150_, v_fvarId_1147_, v___x_1189_);
lean_dec(v___x_1189_);
v___x_1191_ = lean_unbox(v___x_1190_);
v___x_1192_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1191_, v___x_1188_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1193_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1150_, v_snd_1164_);
lean_dec_ref(v_bodyUses_1150_);
v___x_1194_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1193_, v_snd_1187_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = lean_unbox(v___x_1190_);
lean_dec(v___x_1190_);
v___y_1169_ = v_fst_1186_;
v___y_1170_ = v___x_1195_;
v___y_1171_ = v___x_1194_;
goto v___jp_1168_;
}
else
{
uint8_t v___x_1196_; 
lean_dec_ref(v_snd_1187_);
lean_dec(v_snd_1164_);
v___x_1196_ = lean_unbox(v___x_1190_);
lean_dec(v___x_1190_);
v___y_1169_ = v_fst_1186_;
v___y_1170_ = v___x_1196_;
v___y_1171_ = v_bodyUses_1150_;
goto v___jp_1168_;
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_subst_1151_);
lean_dec_ref(v_bodyUses_1150_);
lean_dec(v_val_x3f_1149_);
v_a_1214_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1158_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1158_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1222_, lean_object* v_ty_1223_, lean_object* v_val_x3f_1224_, lean_object* v_bodyUses_1225_, lean_object* v_subst_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1222_, v_ty_1223_, v_val_x3f_1224_, v_bodyUses_1225_, v_subst_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_fvarId_1222_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1233_, lean_object* v_subst_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1233_, v_subst_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_, lean_object* v_fallback_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1242_, v_a_1243_, v_fallback_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_, lean_object* v_fallback_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1246_, v_m_1247_, v_a_1248_, v_fallback_1249_);
lean_dec(v_fallback_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_m_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1252_, v_a_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_m_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1255_, v_m_1256_, v_a_1257_);
lean_dec(v_a_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_msg_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1267_, v_msg_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_, lean_object* v_b_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1276_, v_a_1277_, v_b_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1292_, lean_object* v_a_1293_, lean_object* v_fallback_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1293_, v_fallback_1294_, v_x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_a_1298_, lean_object* v_fallback_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1297_, v_a_1298_, v_fallback_1299_, v_x_1300_);
lean_dec(v_x_1300_);
lean_dec(v_fallback_1299_);
lean_dec(v_a_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1302_, lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1306_, lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1306_, v_a_1307_, v_x_1308_);
lean_dec(v_a_1307_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1311_, v_b_1312_, v_x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1317_, size_t v_i_1318_, size_t v_stop_1319_, lean_object* v_b_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_eq(v_i_1318_, v_stop_1319_);
if (v___x_1326_ == 0)
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_sub(v_i_1318_, v___x_1327_);
v___x_1329_ = lean_array_uget_borrowed(v_as_1317_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
v_i_1318_ = v___x_1328_;
goto _start;
}
else
{
lean_object* v_val_1331_; lean_object* v_fst_1332_; lean_object* v_snd_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
v_fst_1332_ = lean_ctor_get(v_b_1320_, 0);
lean_inc(v_fst_1332_);
v_snd_1333_ = lean_ctor_get(v_b_1320_, 1);
lean_inc(v_snd_1333_);
lean_dec_ref(v_b_1320_);
v___x_1334_ = l_Lean_LocalDecl_fvarId(v_val_1331_);
v___x_1335_ = l_Lean_LocalDecl_type(v_val_1331_);
v___x_1336_ = l_Lean_LocalDecl_value_x3f(v_val_1331_, v___x_1326_);
v___x_1337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1338_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1334_, v___x_1335_, v___x_1336_, v_snd_1333_, v___x_1337_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___x_1334_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v_snd_1340_; lean_object* v_fst_1341_; lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1358_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v_snd_1340_ = lean_ctor_get(v_a_1339_, 1);
lean_inc(v_snd_1340_);
v_fst_1341_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_fst_1341_);
lean_dec(v_a_1339_);
v_fst_1342_ = lean_ctor_get(v_snd_1340_, 0);
v_snd_1343_ = lean_ctor_get(v_snd_1340_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_snd_1340_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1345_ = v_snd_1340_;
v_isShared_1346_ = v_isSharedCheck_1358_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_inc(v_fst_1342_);
lean_dec(v_snd_1340_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1358_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___y_1348_; 
if (lean_obj_tag(v_fst_1342_) == 0)
{
lean_object* v___x_1354_; 
lean_inc(v_val_1331_);
v___x_1354_ = l_Lean_LocalDecl_setType(v_val_1331_, v_fst_1341_);
v___y_1348_ = v___x_1354_;
goto v___jp_1347_;
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_val_1355_ = lean_ctor_get(v_fst_1342_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v_fst_1342_, 1);
lean_inc(v_val_1331_);
v___x_1356_ = l_Lean_LocalDecl_setType(v_val_1331_, v_fst_1341_);
v___x_1357_ = l_Lean_LocalDecl_setValue(v___x_1356_, v_val_1355_);
v___y_1348_ = v___x_1357_;
goto v___jp_1347_;
}
v___jp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_array_push(v_fst_1332_, v___y_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_snd_1343_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v_i_1318_ = v___x_1328_;
v_b_1320_ = v___x_1351_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_fst_1332_);
v_a_1359_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1338_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1338_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
else
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1320_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1368_, lean_object* v_i_1369_, lean_object* v_stop_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
size_t v_i_boxed_1377_; size_t v_stop_boxed_1378_; lean_object* v_res_1379_; 
v_i_boxed_1377_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_stop_boxed_1378_ = lean_unbox_usize(v_stop_1370_);
lean_dec(v_stop_1370_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1368_, v_i_boxed_1377_, v_stop_boxed_1378_, v_b_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec_ref(v_as_1368_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
lean_object* v_cs_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1400_; 
v_cs_1387_ = lean_ctor_get(v_x_1380_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1380_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1389_ = v_x_1380_;
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_cs_1387_);
lean_dec(v_x_1380_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_array_get_size(v_cs_1387_);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_nat_dec_lt(v___x_1392_, v___x_1391_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1395_; 
lean_dec_ref(v_cs_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_x_1381_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_x_1381_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
lean_del_object(v___x_1389_);
v___x_1397_ = lean_usize_of_nat(v___x_1391_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1387_, v___x_1397_, v___x_1398_, v_x_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec_ref(v_cs_1387_);
return v___x_1399_;
}
}
}
else
{
lean_object* v_vs_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1414_; 
v_vs_1401_ = lean_ctor_get(v_x_1380_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1380_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1403_ = v_x_1380_;
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_vs_1401_);
lean_dec(v_x_1380_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_array_get_size(v_vs_1401_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_nat_dec_lt(v___x_1406_, v___x_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1409_; 
lean_dec_ref(v_vs_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set_tag(v___x_1403_, 0);
lean_ctor_set(v___x_1403_, 0, v_x_1381_);
v___x_1409_ = v___x_1403_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_x_1381_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
lean_del_object(v___x_1403_);
v___x_1411_ = lean_usize_of_nat(v___x_1405_);
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1401_, v___x_1411_, v___x_1412_, v_x_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec_ref(v_vs_1401_);
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1415_, size_t v_i_1416_, size_t v_stop_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_eq(v_i_1416_, v_stop_1417_);
if (v___x_1424_ == 0)
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_sub(v_i_1416_, v___x_1425_);
v___x_1427_ = lean_array_uget_borrowed(v_as_1415_, v___x_1426_);
lean_inc(v___x_1427_);
v___x_1428_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1427_, v_b_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v_i_1416_ = v___x_1426_;
v_b_1418_ = v_a_1429_;
goto _start;
}
else
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_b_1418_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1432_, lean_object* v_i_1433_, lean_object* v_stop_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
size_t v_i_boxed_1441_; size_t v_stop_boxed_1442_; lean_object* v_res_1443_; 
v_i_boxed_1441_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_stop_boxed_1442_ = lean_unbox_usize(v_stop_1434_);
lean_dec(v_stop_1434_);
v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1432_, v_i_boxed_1441_, v_stop_boxed_1442_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_as_1432_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1452_, lean_object* v_init_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_root_1459_; lean_object* v_tail_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_root_1459_ = lean_ctor_get(v_t_1452_, 0);
lean_inc_ref(v_root_1459_);
v_tail_1460_ = lean_ctor_get(v_t_1452_, 1);
lean_inc_ref(v_tail_1460_);
lean_dec_ref(v_t_1452_);
v___x_1461_ = lean_array_get_size(v_tail_1460_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_nat_dec_lt(v___x_1462_, v___x_1461_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref(v_tail_1460_);
v___x_1464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1459_, v_init_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1464_;
}
else
{
size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_usize_of_nat(v___x_1461_);
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1460_, v___x_1465_, v___x_1466_, v_init_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec_ref(v_tail_1460_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1467_, 1);
v___x_1469_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1459_, v_a_1468_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1469_;
}
else
{
lean_dec_ref(v_root_1459_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1470_, lean_object* v_init_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1470_, v_init_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1478_, lean_object* v_init_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_decls_1485_; lean_object* v___x_1486_; 
v_decls_1485_ = lean_ctor_get(v_lctx_1478_, 1);
lean_inc_ref(v_decls_1485_);
lean_dec_ref(v_lctx_1478_);
v___x_1486_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1485_, v_init_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1487_, lean_object* v_init_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1487_, v_init_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_bs_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_usize_dec_lt(v_i_1496_, v_sz_1495_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_bs_1497_);
return v___x_1501_;
}
else
{
lean_object* v_v_1502_; lean_object* v___x_1503_; lean_object* v_bs_x27_1504_; lean_object* v_a_1506_; 
v_v_1502_ = lean_array_uget(v_bs_1497_, v_i_1496_);
v___x_1503_ = lean_unsigned_to_nat(0u);
v_bs_x27_1504_ = lean_array_uset(v_bs_1497_, v_i_1496_, v___x_1503_);
if (lean_obj_tag(v_v_1502_) == 0)
{
v_a_1506_ = v_v_1502_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1525_; 
v_isSharedCheck_1525_ = !lean_is_exclusive(v_v_1502_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_v_1502_, 0);
lean_dec(v_unused_1526_);
v___x_1512_ = v_v_1502_;
v_isShared_1513_ = v_isSharedCheck_1525_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_v_1502_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1525_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1514_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1515_ = lean_st_ref_take(v___y_1498_);
v___x_1516_ = lean_array_get_size(v___x_1515_);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_sub(v___x_1516_, v___x_1517_);
v___x_1519_ = lean_array_get_borrowed(v___x_1514_, v___x_1515_, v___x_1518_);
lean_dec(v___x_1518_);
lean_inc(v___x_1519_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1519_);
v___x_1521_ = v___x_1512_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_array_pop(v___x_1515_);
v___x_1523_ = lean_st_ref_put(v___y_1498_, v___x_1522_);
v_a_1506_ = v___x_1521_;
goto v___jp_1505_;
}
}
}
v___jp_1505_:
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1496_, v___x_1507_);
v___x_1509_ = lean_array_uset(v_bs_x27_1504_, v_i_1496_, v_a_1506_);
v_i_1496_ = v___x_1508_;
v_bs_1497_ = v___x_1509_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1527_, lean_object* v_i_1528_, lean_object* v_bs_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
size_t v_sz_boxed_1532_; size_t v_i_boxed_1533_; lean_object* v_res_1534_; 
v_sz_boxed_1532_ = lean_unbox_usize(v_sz_1527_);
lean_dec(v_sz_1527_);
v_i_boxed_1533_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1532_, v_i_boxed_1533_, v_bs_1529_, v___y_1530_);
lean_dec(v___y_1530_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v_cs_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1568_; 
v_cs_1542_ = lean_ctor_get(v_x_1535_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1544_ = v_x_1535_;
v_isShared_1545_ = v_isSharedCheck_1568_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_cs_1542_);
lean_dec(v_x_1535_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1568_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
size_t v_sz_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v_sz_1546_ = lean_array_size(v_cs_1542_);
v___x_1547_ = ((size_t)0ULL);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1546_, v___x_1547_, v_cs_1542_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1559_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v_a_1549_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1544_);
v_a_1560_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1548_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1548_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_vs_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1595_; 
v_vs_1569_ = lean_ctor_get(v_x_1535_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1535_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1571_ = v_x_1535_;
v_isShared_1572_ = v_isSharedCheck_1595_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_vs_1569_);
lean_dec(v_x_1535_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1595_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v_sz_1573_ = lean_array_size(v_vs_1569_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1573_, v___x_1574_, v_vs_1569_, v___y_1536_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1586_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_a_1576_);
v___x_1581_ = v___x_1571_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_del_object(v___x_1571_);
v_a_1587_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1575_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1575_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_bs_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_bs_1598_);
return v___x_1606_;
}
else
{
lean_object* v_v_1607_; lean_object* v___x_1608_; lean_object* v_bs_x27_1609_; lean_object* v___x_1610_; 
v_v_1607_ = lean_array_uget(v_bs_1598_, v_i_1597_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v_bs_x27_1609_ = lean_array_uset(v_bs_1598_, v_i_1597_, v___x_1608_);
v___x_1610_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1607_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1597_, v___x_1612_);
v___x_1614_ = lean_array_uset(v_bs_x27_1609_, v_i_1597_, v_a_1611_);
v_i_1597_ = v___x_1613_;
v_bs_1598_ = v___x_1614_;
goto _start;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_bs_x27_1609_);
v_a_1616_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1610_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1610_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_bs_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
size_t v_sz_boxed_1633_; size_t v_i_boxed_1634_; lean_object* v_res_1635_; 
v_sz_boxed_1633_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1634_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1633_, v_i_boxed_1634_, v_bs_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_root_1651_; lean_object* v_tail_1652_; lean_object* v_size_1653_; size_t v_shift_1654_; lean_object* v_tailOff_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1691_; 
v_root_1651_ = lean_ctor_get(v_t_1644_, 0);
v_tail_1652_ = lean_ctor_get(v_t_1644_, 1);
v_size_1653_ = lean_ctor_get(v_t_1644_, 2);
v_shift_1654_ = lean_ctor_get_usize(v_t_1644_, 4);
v_tailOff_1655_ = lean_ctor_get(v_t_1644_, 3);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_t_1644_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1657_ = v_t_1644_;
v_isShared_1658_ = v_isSharedCheck_1691_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_tailOff_1655_);
lean_inc(v_size_1653_);
lean_inc(v_tail_1652_);
lean_inc(v_root_1651_);
lean_dec(v_t_1644_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1691_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1651_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; size_t v_sz_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v_sz_1661_ = lean_array_size(v_tail_1652_);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1661_, v___x_1662_, v_tail_1652_, v___y_1645_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1664_);
lean_ctor_set(v___x_1657_, 0, v_a_1660_);
v___x_1669_ = v___x_1657_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_a_1664_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_size_1653_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_tailOff_1655_);
lean_ctor_set_usize(v_reuseFailAlloc_1673_, 4, v_shift_1654_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_a_1660_);
lean_del_object(v___x_1657_);
lean_dec(v_tailOff_1655_);
lean_dec(v_size_1653_);
v_a_1675_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1663_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1663_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1657_);
lean_dec(v_tailOff_1655_);
lean_dec(v_size_1653_);
lean_dec_ref(v_tail_1652_);
v_a_1683_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1659_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1659_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1700_, lean_object* v_targetUses_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_decls_1707_; lean_object* v_fvarIdToDecl_1708_; lean_object* v_auxDeclToFullName_1709_; lean_object* v_size_1710_; lean_object* v_decls_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_decls_1707_ = lean_ctor_get(v_ctx_1700_, 1);
lean_inc_ref(v_decls_1707_);
v_fvarIdToDecl_1708_ = lean_ctor_get(v_ctx_1700_, 0);
lean_inc_ref(v_fvarIdToDecl_1708_);
v_auxDeclToFullName_1709_ = lean_ctor_get(v_ctx_1700_, 2);
lean_inc(v_auxDeclToFullName_1709_);
v_size_1710_ = lean_ctor_get(v_decls_1707_, 2);
v_decls_1711_ = lean_mk_empty_array_with_capacity(v_size_1710_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_decls_1711_);
lean_ctor_set(v___x_1712_, 1, v_targetUses_1701_);
v___x_1713_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1700_, v___x_1712_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v_fst_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v_fst_1715_ = lean_ctor_get(v_a_1714_, 0);
lean_inc(v_fst_1715_);
lean_dec(v_a_1714_);
v___x_1716_ = lean_st_mk_ref(v_fst_1715_);
v___x_1717_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1707_, v___x_1716_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1722_ = lean_st_ref_get(v___x_1716_);
lean_dec(v___x_1716_);
lean_dec(v___x_1722_);
v___x_1723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1723_, 0, v_fvarIdToDecl_1708_);
lean_ctor_set(v___x_1723_, 1, v_a_1718_);
lean_ctor_set(v___x_1723_, 2, v_auxDeclToFullName_1709_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v___x_1716_);
lean_dec(v_auxDeclToFullName_1709_);
lean_dec_ref(v_fvarIdToDecl_1708_);
v_a_1728_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1717_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1717_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_auxDeclToFullName_1709_);
lean_dec_ref(v_fvarIdToDecl_1708_);
lean_dec_ref(v_decls_1707_);
v_a_1736_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1713_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1713_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1744_, lean_object* v_targetUses_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1744_, v_targetUses_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_bs_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1752_, v_i_1753_, v_bs_1754_, v___y_1755_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_bs_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; lean_object* v_res_1773_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1771_, v_i_boxed_1772_, v_bs_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
return v_res_1773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1774_, lean_object* v_rhs_1775_, uint8_t v_elimTrivial_1776_){
_start:
{
uint8_t v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = 2;
v___x_1778_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1774_, v___x_1777_);
if (v___x_1778_ == 0)
{
return v___x_1778_;
}
else
{
if (v_elimTrivial_1776_ == 0)
{
return v___x_1778_;
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1775_);
if (v___x_1779_ == 0)
{
return v___x_1778_;
}
else
{
uint8_t v___x_1780_; 
v___x_1780_ = 0;
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1781_, lean_object* v_rhs_1782_, lean_object* v_elimTrivial_1783_){
_start:
{
uint8_t v_u_boxed_1784_; uint8_t v_elimTrivial_boxed_1785_; uint8_t v_res_1786_; lean_object* v_r_1787_; 
v_u_boxed_1784_ = lean_unbox(v_u_1781_);
v_elimTrivial_boxed_1785_ = lean_unbox(v_elimTrivial_1783_);
v_res_1786_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1784_, v_rhs_1782_, v_elimTrivial_boxed_1785_);
lean_dec_ref(v_rhs_1782_);
v_r_1787_ = lean_box(v_res_1786_);
return v_r_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1790_, lean_object* v_e_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
if (lean_obj_tag(v_e_1791_) == 8)
{
lean_object* v_type_1798_; 
v_type_1798_ = lean_ctor_get(v_e_1791_, 1);
if (lean_obj_tag(v_type_1798_) == 10)
{
lean_object* v_value_1799_; lean_object* v_body_1800_; lean_object* v_data_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v_uses_1805_; uint8_t v___x_1806_; 
v_value_1799_ = lean_ctor_get(v_e_1791_, 2);
v_body_1800_ = lean_ctor_get(v_e_1791_, 3);
v_data_1801_ = lean_ctor_get(v_type_1798_, 0);
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1803_ = lean_unsigned_to_nat(2u);
v___x_1804_ = l_Lean_KVMap_getNat(v_data_1801_, v___x_1802_, v___x_1803_);
v_uses_1805_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1804_);
lean_dec(v___x_1804_);
v___x_1806_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1805_, v_value_1799_, v_elimTrivial_1790_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_expr_instantiate1(v_body_1800_, v_value_1799_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1816_, lean_object* v_e_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_elimTrivial_boxed_1824_; lean_object* v_res_1825_; 
v_elimTrivial_boxed_1824_ = lean_unbox(v_elimTrivial_1816_);
v_res_1825_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1824_, v_e_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v_e_1817_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_e_1826_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
return v_res_1842_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = l_Lean_maxRecDepthErrorMessage;
v___x_1849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1851_ = l_Lean_MessageData_ofFormat(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1853_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1854_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_ref_1855_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___y_1872_; lean_object* v_toCold_1881_; lean_object* v_currRecDepth_1882_; lean_object* v_ref_1883_; uint16_t v_optionFlags_1884_; uint8_t v_suppressElabErrors_1885_; uint8_t v_isRecordingDeps_1886_; lean_object* v_maxRecDepth_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_toCold_1881_ = lean_ctor_get(v___y_1868_, 0);
v_currRecDepth_1882_ = lean_ctor_get(v___y_1868_, 1);
v_ref_1883_ = lean_ctor_get(v___y_1868_, 2);
v_optionFlags_1884_ = lean_ctor_get_uint16(v___y_1868_, sizeof(void*)*3);
v_suppressElabErrors_1885_ = lean_ctor_get_uint8(v___y_1868_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1886_ = lean_ctor_get_uint8(v___y_1868_, sizeof(void*)*3 + 3);
v_maxRecDepth_1892_ = lean_ctor_get(v_toCold_1881_, 3);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_nat_dec_eq(v_maxRecDepth_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_eq(v_currRecDepth_1882_, v_maxRecDepth_1892_);
if (v___x_1895_ == 0)
{
goto v___jp_1887_;
}
else
{
lean_object* v___x_1896_; 
lean_dec_ref(v_x_1863_);
lean_inc(v_ref_1883_);
v___x_1896_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1883_);
v___y_1872_ = v___x_1896_;
goto v___jp_1871_;
}
}
else
{
goto v___jp_1887_;
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1872_) == 0)
{
return v___y_1872_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___y_1872_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___y_1872_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___y_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___y_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
v___jp_1887_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_unsigned_to_nat(1u);
v___x_1889_ = lean_nat_add(v_currRecDepth_1882_, v___x_1888_);
lean_inc(v_ref_1883_);
lean_inc_ref(v_toCold_1881_);
v___x_1890_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1890_, 0, v_toCold_1881_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
lean_ctor_set(v___x_1890_, 2, v_ref_1883_);
lean_ctor_set_uint16(v___x_1890_, sizeof(void*)*3, v_optionFlags_1884_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*3 + 2, v_suppressElabErrors_1885_);
lean_ctor_set_uint8(v___x_1890_, sizeof(void*)*3 + 3, v_isRecordingDeps_1886_);
lean_inc(v___y_1869_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc(v___y_1864_);
v___x_1891_ = lean_apply_7(v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___x_1890_, v___y_1869_, lean_box(0));
v___y_1872_ = v___x_1891_;
goto v___jp_1871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v_b_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1908_);
lean_inc(v___y_1907_);
v___x_1915_ = lean_apply_8(v_k_1906_, v_b_1909_, v___y_1907_, v___y_1908_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, lean_box(0));
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1916_, v___y_1917_, v___y_1918_, v_b_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1926_, lean_object* v_type_1927_, lean_object* v_val_1928_, lean_object* v_k_1929_, uint8_t v_nondep_1930_, uint8_t v_kind_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___f_1939_; lean_object* v___x_1940_; 
lean_inc(v___y_1933_);
lean_inc(v___y_1932_);
v___f_1939_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1939_, 0, v_k_1929_);
lean_closure_set(v___f_1939_, 1, v___y_1932_);
lean_closure_set(v___f_1939_, 2, v___y_1933_);
v___x_1940_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1926_, v_type_1927_, v_val_1928_, v___f_1939_, v_nondep_1930_, v_kind_1931_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1940_) == 0)
{
return v___x_1940_;
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1949_, lean_object* v_type_1950_, lean_object* v_val_1951_, lean_object* v_k_1952_, lean_object* v_nondep_1953_, lean_object* v_kind_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v_nondep_boxed_1962_; uint8_t v_kind_boxed_1963_; lean_object* v_res_1964_; 
v_nondep_boxed_1962_ = lean_unbox(v_nondep_1953_);
v_kind_boxed_1963_ = lean_unbox(v_kind_1954_);
v_res_1964_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1949_, v_type_1950_, v_val_1951_, v_k_1952_, v_nondep_boxed_1962_, v_kind_boxed_1963_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_1965_, uint8_t v_bi_1966_, lean_object* v_type_1967_, lean_object* v_k_1968_, uint8_t v_kind_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___f_1977_; lean_object* v___x_1978_; 
lean_inc(v___y_1971_);
lean_inc(v___y_1970_);
v___f_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1977_, 0, v_k_1968_);
lean_closure_set(v___f_1977_, 1, v___y_1970_);
lean_closure_set(v___f_1977_, 2, v___y_1971_);
v___x_1978_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1965_, v_bi_1966_, v_type_1967_, v___f_1977_, v_kind_1969_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
return v___x_1978_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_1987_, lean_object* v_bi_1988_, lean_object* v_type_1989_, lean_object* v_k_1990_, lean_object* v_kind_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v_bi_boxed_1999_; uint8_t v_kind_boxed_2000_; lean_object* v_res_2001_; 
v_bi_boxed_1999_ = lean_unbox(v_bi_1988_);
v_kind_boxed_2000_ = lean_unbox(v_kind_1991_);
v_res_2001_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1987_, v_bi_boxed_1999_, v_type_1989_, v_k_1990_, v_kind_boxed_2000_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v___y_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2(lean_object* v___x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2002_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2___boxed(lean_object* v___x_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2(v___x_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_apply_1(v_x_2019_, lean_box(0));
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2028_, v_x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
return v_x_2037_;
}
else
{
lean_object* v_key_2039_; lean_object* v_value_2040_; lean_object* v_tail_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2064_; 
v_key_2039_ = lean_ctor_get(v_x_2038_, 0);
v_value_2040_ = lean_ctor_get(v_x_2038_, 1);
v_tail_2041_ = lean_ctor_get(v_x_2038_, 2);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2043_ = v_x_2038_;
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_tail_2041_);
lean_inc(v_value_2040_);
lean_inc(v_key_2039_);
lean_dec(v_x_2038_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; uint64_t v___x_2046_; uint64_t v___x_2047_; uint64_t v___x_2048_; uint64_t v_fold_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; uint64_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2045_ = lean_array_get_size(v_x_2037_);
v___x_2046_ = l_Lean_ExprStructEq_hash(v_key_2039_);
v___x_2047_ = 32ULL;
v___x_2048_ = lean_uint64_shift_right(v___x_2046_, v___x_2047_);
v_fold_2049_ = lean_uint64_xor(v___x_2046_, v___x_2048_);
v___x_2050_ = 16ULL;
v___x_2051_ = lean_uint64_shift_right(v_fold_2049_, v___x_2050_);
v___x_2052_ = lean_uint64_xor(v_fold_2049_, v___x_2051_);
v___x_2053_ = lean_uint64_to_usize(v___x_2052_);
v___x_2054_ = lean_usize_of_nat(v___x_2045_);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_sub(v___x_2054_, v___x_2055_);
v___x_2057_ = lean_usize_land(v___x_2053_, v___x_2056_);
v___x_2058_ = lean_array_uget_borrowed(v_x_2037_, v___x_2057_);
lean_inc(v___x_2058_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v___x_2058_);
v___x_2060_ = v___x_2043_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_key_2039_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_value_2040_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_array_uset(v_x_2037_, v___x_2057_, v___x_2060_);
v_x_2037_ = v___x_2061_;
v_x_2038_ = v_tail_2041_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2065_, lean_object* v_source_2066_, lean_object* v_target_2067_){
_start:
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_array_get_size(v_source_2066_);
v___x_2069_ = lean_nat_dec_lt(v_i_2065_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_source_2066_);
lean_dec(v_i_2065_);
return v_target_2067_;
}
else
{
lean_object* v_es_2070_; lean_object* v___x_2071_; lean_object* v_source_2072_; lean_object* v_target_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_es_2070_ = lean_array_fget(v_source_2066_, v_i_2065_);
v___x_2071_ = lean_box(0);
v_source_2072_ = lean_array_fset(v_source_2066_, v_i_2065_, v___x_2071_);
v_target_2073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2067_, v_es_2070_);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_add(v_i_2065_, v___x_2074_);
lean_dec(v_i_2065_);
v_i_2065_ = v___x_2075_;
v_source_2066_ = v_source_2072_;
v_target_2067_ = v_target_2073_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v_nbuckets_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2078_ = lean_array_get_size(v_data_2077_);
v___x_2079_ = lean_unsigned_to_nat(2u);
v_nbuckets_2080_ = lean_nat_mul(v___x_2078_, v___x_2079_);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_mk_array(v_nbuckets_2080_, v___x_2082_);
v___x_2084_ = lean_array_propagate_mark(v_data_2077_, v___x_2083_);
v___x_2085_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2081_, v_data_2077_, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2086_, lean_object* v_b_2087_, lean_object* v_x_2088_){
_start:
{
if (lean_obj_tag(v_x_2088_) == 0)
{
lean_dec(v_b_2087_);
lean_dec_ref(v_a_2086_);
return v_x_2088_;
}
else
{
lean_object* v_key_2089_; lean_object* v_value_2090_; lean_object* v_tail_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2103_; 
v_key_2089_ = lean_ctor_get(v_x_2088_, 0);
v_value_2090_ = lean_ctor_get(v_x_2088_, 1);
v_tail_2091_ = lean_ctor_get(v_x_2088_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2088_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2093_ = v_x_2088_;
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_tail_2091_);
lean_inc(v_value_2090_);
lean_inc(v_key_2089_);
lean_dec(v_x_2088_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2103_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Lean_ExprStructEq_beq(v_key_2089_, v_a_2086_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2086_, v_b_2087_, v_tail_2091_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 2, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_key_2089_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_value_2090_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
lean_object* v___x_2101_; 
lean_dec(v_value_2090_);
lean_dec(v_key_2089_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v_b_2087_);
lean_ctor_set(v___x_2093_, 0, v_a_2086_);
v___x_2101_ = v___x_2093_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2086_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_b_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_tail_2091_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2104_, lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
uint8_t v___x_2106_; 
v___x_2106_ = 0;
return v___x_2106_;
}
else
{
lean_object* v_key_2107_; lean_object* v_tail_2108_; uint8_t v___x_2109_; 
v_key_2107_ = lean_ctor_get(v_x_2105_, 0);
v_tail_2108_ = lean_ctor_get(v_x_2105_, 2);
v___x_2109_ = l_Lean_ExprStructEq_beq(v_key_2107_, v_a_2104_);
if (v___x_2109_ == 0)
{
v_x_2105_ = v_tail_2108_;
goto _start;
}
else
{
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2111_, v_x_2112_);
lean_dec(v_x_2112_);
lean_dec_ref(v_a_2111_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2115_, lean_object* v_a_2116_, lean_object* v_b_2117_){
_start:
{
lean_object* v_size_2118_; lean_object* v_buckets_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2162_; 
v_size_2118_ = lean_ctor_get(v_m_2115_, 0);
v_buckets_2119_ = lean_ctor_get(v_m_2115_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_m_2115_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2121_ = v_m_2115_;
v_isShared_2122_ = v_isSharedCheck_2162_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_buckets_2119_);
lean_inc(v_size_2118_);
lean_dec(v_m_2115_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2162_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; uint64_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v_fold_2127_; uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; lean_object* v_bkt_2136_; uint8_t v___x_2137_; 
v___x_2123_ = lean_array_get_size(v_buckets_2119_);
v___x_2124_ = l_Lean_ExprStructEq_hash(v_a_2116_);
v___x_2125_ = 32ULL;
v___x_2126_ = lean_uint64_shift_right(v___x_2124_, v___x_2125_);
v_fold_2127_ = lean_uint64_xor(v___x_2124_, v___x_2126_);
v___x_2128_ = 16ULL;
v___x_2129_ = lean_uint64_shift_right(v_fold_2127_, v___x_2128_);
v___x_2130_ = lean_uint64_xor(v_fold_2127_, v___x_2129_);
v___x_2131_ = lean_uint64_to_usize(v___x_2130_);
v___x_2132_ = lean_usize_of_nat(v___x_2123_);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_sub(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_usize_land(v___x_2131_, v___x_2134_);
v_bkt_2136_ = lean_array_uget_borrowed(v_buckets_2119_, v___x_2135_);
v___x_2137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2116_, v_bkt_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v_size_x27_2139_; lean_object* v___x_2140_; lean_object* v_buckets_x27_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2138_ = lean_unsigned_to_nat(1u);
v_size_x27_2139_ = lean_nat_add(v_size_2118_, v___x_2138_);
lean_dec(v_size_2118_);
lean_inc(v_bkt_2136_);
v___x_2140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2116_);
lean_ctor_set(v___x_2140_, 1, v_b_2117_);
lean_ctor_set(v___x_2140_, 2, v_bkt_2136_);
v_buckets_x27_2141_ = lean_array_uset(v_buckets_2119_, v___x_2135_, v___x_2140_);
v___x_2142_ = lean_unsigned_to_nat(4u);
v___x_2143_ = lean_nat_mul(v_size_x27_2139_, v___x_2142_);
v___x_2144_ = lean_unsigned_to_nat(3u);
v___x_2145_ = lean_nat_div(v___x_2143_, v___x_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_array_get_size(v_buckets_x27_2141_);
v___x_2147_ = lean_nat_dec_le(v___x_2145_, v___x_2146_);
lean_dec(v___x_2145_);
if (v___x_2147_ == 0)
{
lean_object* v_val_2148_; lean_object* v___x_2150_; 
v_val_2148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2141_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v_val_2148_);
lean_ctor_set(v___x_2121_, 0, v_size_x27_2139_);
v___x_2150_ = v___x_2121_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_size_x27_2139_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_val_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
lean_object* v___x_2153_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v_buckets_x27_2141_);
lean_ctor_set(v___x_2121_, 0, v_size_x27_2139_);
v___x_2153_ = v___x_2121_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_size_x27_2139_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_buckets_x27_2141_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v_buckets_x27_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_inc(v_bkt_2136_);
v___x_2155_ = lean_box(0);
v_buckets_x27_2156_ = lean_array_uset(v_buckets_2119_, v___x_2135_, v___x_2155_);
v___x_2157_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2116_, v_b_2117_, v_bkt_2136_);
v___x_2158_ = lean_array_uset(v_buckets_x27_2156_, v___x_2135_, v___x_2157_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2158_);
v___x_2160_ = v___x_2121_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_size_2118_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2163_, lean_object* v_e_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = lean_st_ref_take(v_a_2163_);
v___x_2168_ = lean_box(0);
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2167_, v_e_2164_, v_a_2165_);
v___x_2170_ = lean_st_ref_put(v_a_2163_, v___x_2169_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2171_, lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2171_, v_e_2172_, v_a_2173_);
lean_dec(v_a_2171_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_2176_, lean_object* v_x_2177_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 0)
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_box(0);
return v___x_2178_;
}
else
{
lean_object* v_key_2179_; lean_object* v_value_2180_; lean_object* v_tail_2181_; uint8_t v___x_2182_; 
v_key_2179_ = lean_ctor_get(v_x_2177_, 0);
v_value_2180_ = lean_ctor_get(v_x_2177_, 1);
v_tail_2181_ = lean_ctor_get(v_x_2177_, 2);
v___x_2182_ = l_Lean_ExprStructEq_beq(v_key_2179_, v_a_2176_);
if (v___x_2182_ == 0)
{
v_x_2177_ = v_tail_2181_;
goto _start;
}
else
{
lean_object* v___x_2184_; 
lean_inc(v_value_2180_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_value_2180_);
return v___x_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2185_, v_x_2186_);
lean_dec(v_x_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg(lean_object* v_m_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_buckets_2190_; lean_object* v___x_2191_; uint64_t v___x_2192_; uint64_t v___x_2193_; uint64_t v___x_2194_; uint64_t v_fold_2195_; uint64_t v___x_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_buckets_2190_ = lean_ctor_get(v_m_2188_, 1);
v___x_2191_ = lean_array_get_size(v_buckets_2190_);
v___x_2192_ = l_Lean_ExprStructEq_hash(v_a_2189_);
v___x_2193_ = 32ULL;
v___x_2194_ = lean_uint64_shift_right(v___x_2192_, v___x_2193_);
v_fold_2195_ = lean_uint64_xor(v___x_2192_, v___x_2194_);
v___x_2196_ = 16ULL;
v___x_2197_ = lean_uint64_shift_right(v_fold_2195_, v___x_2196_);
v___x_2198_ = lean_uint64_xor(v_fold_2195_, v___x_2197_);
v___x_2199_ = lean_uint64_to_usize(v___x_2198_);
v___x_2200_ = lean_usize_of_nat(v___x_2191_);
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_sub(v___x_2200_, v___x_2201_);
v___x_2203_ = lean_usize_land(v___x_2199_, v___x_2202_);
v___x_2204_ = lean_array_uget_borrowed(v_buckets_2190_, v___x_2203_);
v___x_2205_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2189_, v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg(v_m_2206_, v_a_2207_);
lean_dec_ref(v_a_2207_);
lean_dec_ref(v_m_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2209_, lean_object* v_pre_2210_, lean_object* v_post_2211_, lean_object* v_usedLetOnly_2212_, lean_object* v_skipConstInApp_2213_, lean_object* v_skipInstances_2214_, lean_object* v_postApp_2215_, lean_object* v_body_2216_, lean_object* v_x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
uint8_t v_usedLetOnly_boxed_2225_; uint8_t v_skipConstInApp_boxed_2226_; uint8_t v_skipInstances_boxed_2227_; lean_object* v_res_2228_; 
v_usedLetOnly_boxed_2225_ = lean_unbox(v_usedLetOnly_2212_);
v_skipConstInApp_boxed_2226_ = lean_unbox(v_skipConstInApp_2213_);
v_skipInstances_boxed_2227_ = lean_unbox(v_skipInstances_2214_);
v_res_2228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2209_, v_pre_2210_, v_post_2211_, v_usedLetOnly_boxed_2225_, v_skipConstInApp_boxed_2226_, v_skipInstances_boxed_2227_, v_postApp_2215_, v_body_2216_, v_x_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec(v___y_2218_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2232_, lean_object* v_pre_2233_, lean_object* v_post_2234_, uint8_t v_usedLetOnly_2235_, uint8_t v_skipConstInApp_2236_, uint8_t v_skipInstances_2237_, lean_object* v_postApp_2238_, lean_object* v_body_2239_, lean_object* v_x_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_array_push(v_fvars_2232_, v_x_2240_);
v___x_2249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2233_, v_post_2234_, v_usedLetOnly_2235_, v_skipConstInApp_2236_, v_skipInstances_2237_, v_postApp_2238_, v___x_2248_, v_body_2239_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2250_, lean_object* v_pre_2251_, lean_object* v_post_2252_, lean_object* v_usedLetOnly_2253_, lean_object* v_skipConstInApp_2254_, lean_object* v_skipInstances_2255_, lean_object* v_postApp_2256_, lean_object* v_body_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_usedLetOnly_boxed_2266_; uint8_t v_skipConstInApp_boxed_2267_; uint8_t v_skipInstances_boxed_2268_; lean_object* v_res_2269_; 
v_usedLetOnly_boxed_2266_ = lean_unbox(v_usedLetOnly_2253_);
v_skipConstInApp_boxed_2267_ = lean_unbox(v_skipConstInApp_2254_);
v_skipInstances_boxed_2268_ = lean_unbox(v_skipInstances_2255_);
v_res_2269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2250_, v_pre_2251_, v_post_2252_, v_usedLetOnly_boxed_2266_, v_skipConstInApp_boxed_2267_, v_skipInstances_boxed_2268_, v_postApp_2256_, v_body_2257_, v_x_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_pre_2270_, lean_object* v_post_2271_, uint8_t v_usedLetOnly_2272_, uint8_t v_skipConstInApp_2273_, uint8_t v_skipInstances_2274_, lean_object* v_postApp_2275_, lean_object* v_e_2276_, lean_object* v_a_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
lean_inc_ref(v_post_2271_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
lean_inc(v___y_2280_);
lean_inc_ref(v___y_2279_);
lean_inc(v___y_2278_);
lean_inc_ref(v_e_2276_);
v___x_2284_ = lean_apply_7(v_post_2271_, v_e_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, lean_box(0));
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2303_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2303_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2303_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
switch(lean_obj_tag(v_a_2285_))
{
case 0:
{
lean_object* v_e_2289_; lean_object* v___x_2291_; 
lean_dec_ref(v_e_2276_);
lean_dec_ref(v_postApp_2275_);
lean_dec_ref(v_post_2271_);
lean_dec_ref(v_pre_2270_);
v_e_2289_ = lean_ctor_get(v_a_2285_, 0);
lean_inc_ref(v_e_2289_);
lean_dec_ref_known(v_a_2285_, 1);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_e_2289_);
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_e_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
case 1:
{
lean_object* v_e_2293_; lean_object* v___x_2294_; 
lean_del_object(v___x_2287_);
lean_dec_ref(v_e_2276_);
v_e_2293_ = lean_ctor_get(v_a_2285_, 0);
lean_inc_ref(v_e_2293_);
lean_dec_ref_known(v_a_2285_, 1);
v___x_2294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2270_, v_post_2271_, v_usedLetOnly_2272_, v_skipConstInApp_2273_, v_skipInstances_2274_, v_postApp_2275_, v_e_2293_, v_a_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2294_;
}
default: 
{
lean_object* v_e_x3f_2295_; 
lean_dec_ref(v_postApp_2275_);
lean_dec_ref(v_post_2271_);
lean_dec_ref(v_pre_2270_);
v_e_x3f_2295_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_e_x3f_2295_);
lean_dec_ref_known(v_a_2285_, 1);
if (lean_obj_tag(v_e_x3f_2295_) == 0)
{
lean_object* v___x_2297_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_e_2276_);
v___x_2297_ = v___x_2287_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_e_2276_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
else
{
lean_object* v_val_2299_; lean_object* v___x_2301_; 
lean_dec_ref(v_e_2276_);
v_val_2299_ = lean_ctor_get(v_e_x3f_2295_, 0);
lean_inc(v_val_2299_);
lean_dec_ref_known(v_e_x3f_2295_, 1);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_val_2299_);
v___x_2301_ = v___x_2287_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_val_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_e_2276_);
lean_dec_ref(v_postApp_2275_);
lean_dec_ref(v_post_2271_);
lean_dec_ref(v_pre_2270_);
v_a_2304_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2284_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2284_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2312_, lean_object* v_post_2313_, uint8_t v_usedLetOnly_2314_, uint8_t v_skipConstInApp_2315_, uint8_t v_skipInstances_2316_, lean_object* v_postApp_2317_, lean_object* v_fvars_2318_, lean_object* v_e_2319_, lean_object* v_a_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
if (lean_obj_tag(v_e_2319_) == 6)
{
lean_object* v_binderName_2327_; lean_object* v_binderType_2328_; lean_object* v_body_2329_; uint8_t v_binderInfo_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_binderName_2327_ = lean_ctor_get(v_e_2319_, 0);
lean_inc(v_binderName_2327_);
v_binderType_2328_ = lean_ctor_get(v_e_2319_, 1);
lean_inc_ref(v_binderType_2328_);
v_body_2329_ = lean_ctor_get(v_e_2319_, 2);
lean_inc_ref(v_body_2329_);
v_binderInfo_2330_ = lean_ctor_get_uint8(v_e_2319_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2319_, 3);
v___x_2331_ = lean_box(v_usedLetOnly_2314_);
v___x_2332_ = lean_box(v_skipConstInApp_2315_);
v___x_2333_ = lean_box(v_skipInstances_2316_);
lean_inc_ref(v_postApp_2317_);
lean_inc_ref(v_post_2313_);
lean_inc_ref(v_pre_2312_);
lean_inc_ref(v_fvars_2318_);
v___f_2334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2334_, 0, v_fvars_2318_);
lean_closure_set(v___f_2334_, 1, v_pre_2312_);
lean_closure_set(v___f_2334_, 2, v_post_2313_);
lean_closure_set(v___f_2334_, 3, v___x_2331_);
lean_closure_set(v___f_2334_, 4, v___x_2332_);
lean_closure_set(v___f_2334_, 5, v___x_2333_);
lean_closure_set(v___f_2334_, 6, v_postApp_2317_);
lean_closure_set(v___f_2334_, 7, v_body_2329_);
v___x_2335_ = lean_expr_instantiate_rev(v_binderType_2328_, v_fvars_2318_);
lean_dec_ref(v_fvars_2318_);
lean_dec_ref(v_binderType_2328_);
v___x_2336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2312_, v_post_2313_, v_usedLetOnly_2314_, v_skipConstInApp_2315_, v_skipInstances_2316_, v_postApp_2317_, v___x_2335_, v_a_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = 0;
v___x_2339_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2327_, v_binderInfo_2330_, v_a_2337_, v___f_2334_, v___x_2338_, v_a_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2339_;
}
else
{
lean_dec_ref(v___f_2334_);
lean_dec(v_binderName_2327_);
return v___x_2336_;
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_expr_instantiate_rev(v_e_2319_, v_fvars_2318_);
lean_dec_ref(v_e_2319_);
lean_inc_ref(v_postApp_2317_);
lean_inc_ref(v_post_2313_);
lean_inc_ref(v_pre_2312_);
v___x_2341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2312_, v_post_2313_, v_usedLetOnly_2314_, v_skipConstInApp_2315_, v_skipInstances_2316_, v_postApp_2317_, v___x_2340_, v_a_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; uint8_t v___x_2343_; uint8_t v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = 0;
v___x_2344_ = 1;
v___x_2345_ = 1;
v___x_2346_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2318_, v_a_2342_, v___x_2343_, v_usedLetOnly_2314_, v___x_2343_, v___x_2344_, v___x_2345_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec_ref(v_fvars_2318_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2312_, v_post_2313_, v_usedLetOnly_2314_, v_skipConstInApp_2315_, v_skipInstances_2316_, v_postApp_2317_, v_a_2347_, v_a_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2348_;
}
else
{
lean_dec_ref(v_postApp_2317_);
lean_dec_ref(v_post_2313_);
lean_dec_ref(v_pre_2312_);
return v___x_2346_;
}
}
else
{
lean_dec_ref(v_fvars_2318_);
lean_dec_ref(v_postApp_2317_);
lean_dec_ref(v_post_2313_);
lean_dec_ref(v_pre_2312_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2349_, lean_object* v_pre_2350_, lean_object* v_post_2351_, uint8_t v_usedLetOnly_2352_, uint8_t v_skipConstInApp_2353_, uint8_t v_skipInstances_2354_, lean_object* v_postApp_2355_, lean_object* v_body_2356_, lean_object* v_x_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_array_push(v_fvars_2349_, v_x_2357_);
v___x_2366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2350_, v_post_2351_, v_usedLetOnly_2352_, v_skipConstInApp_2353_, v_skipInstances_2354_, v_postApp_2355_, v___x_2365_, v_body_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2367_, lean_object* v_pre_2368_, lean_object* v_post_2369_, lean_object* v_usedLetOnly_2370_, lean_object* v_skipConstInApp_2371_, lean_object* v_skipInstances_2372_, lean_object* v_postApp_2373_, lean_object* v_body_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v_usedLetOnly_boxed_2383_; uint8_t v_skipConstInApp_boxed_2384_; uint8_t v_skipInstances_boxed_2385_; lean_object* v_res_2386_; 
v_usedLetOnly_boxed_2383_ = lean_unbox(v_usedLetOnly_2370_);
v_skipConstInApp_boxed_2384_ = lean_unbox(v_skipConstInApp_2371_);
v_skipInstances_boxed_2385_ = lean_unbox(v_skipInstances_2372_);
v_res_2386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2367_, v_pre_2368_, v_post_2369_, v_usedLetOnly_boxed_2383_, v_skipConstInApp_boxed_2384_, v_skipInstances_boxed_2385_, v_postApp_2373_, v_body_2374_, v_x_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2387_, lean_object* v_post_2388_, uint8_t v_usedLetOnly_2389_, uint8_t v_skipConstInApp_2390_, uint8_t v_skipInstances_2391_, lean_object* v_postApp_2392_, lean_object* v_fvars_2393_, lean_object* v_e_2394_, lean_object* v_a_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
if (lean_obj_tag(v_e_2394_) == 8)
{
lean_object* v_declName_2402_; lean_object* v_type_2403_; lean_object* v_value_2404_; lean_object* v_body_2405_; uint8_t v_nondep_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_declName_2402_ = lean_ctor_get(v_e_2394_, 0);
lean_inc(v_declName_2402_);
v_type_2403_ = lean_ctor_get(v_e_2394_, 1);
lean_inc_ref(v_type_2403_);
v_value_2404_ = lean_ctor_get(v_e_2394_, 2);
lean_inc_ref(v_value_2404_);
v_body_2405_ = lean_ctor_get(v_e_2394_, 3);
lean_inc_ref(v_body_2405_);
v_nondep_2406_ = lean_ctor_get_uint8(v_e_2394_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2394_, 4);
v___x_2407_ = lean_box(v_usedLetOnly_2389_);
v___x_2408_ = lean_box(v_skipConstInApp_2390_);
v___x_2409_ = lean_box(v_skipInstances_2391_);
lean_inc_ref_n(v_postApp_2392_, 2);
lean_inc_ref_n(v_post_2388_, 2);
lean_inc_ref_n(v_pre_2387_, 2);
lean_inc_ref(v_fvars_2393_);
v___f_2410_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2410_, 0, v_fvars_2393_);
lean_closure_set(v___f_2410_, 1, v_pre_2387_);
lean_closure_set(v___f_2410_, 2, v_post_2388_);
lean_closure_set(v___f_2410_, 3, v___x_2407_);
lean_closure_set(v___f_2410_, 4, v___x_2408_);
lean_closure_set(v___f_2410_, 5, v___x_2409_);
lean_closure_set(v___f_2410_, 6, v_postApp_2392_);
lean_closure_set(v___f_2410_, 7, v_body_2405_);
v___x_2411_ = lean_expr_instantiate_rev(v_type_2403_, v_fvars_2393_);
lean_dec_ref(v_type_2403_);
v___x_2412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2387_, v_post_2388_, v_usedLetOnly_2389_, v_skipConstInApp_2390_, v_skipInstances_2391_, v_postApp_2392_, v___x_2411_, v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = lean_expr_instantiate_rev(v_value_2404_, v_fvars_2393_);
lean_dec_ref(v_fvars_2393_);
lean_dec_ref(v_value_2404_);
v___x_2415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2387_, v_post_2388_, v_usedLetOnly_2389_, v_skipConstInApp_2390_, v_skipInstances_2391_, v_postApp_2392_, v___x_2414_, v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = 0;
v___x_2418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2402_, v_a_2413_, v_a_2416_, v___f_2410_, v_nondep_2406_, v___x_2417_, v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2418_;
}
else
{
lean_dec(v_a_2413_);
lean_dec_ref(v___f_2410_);
lean_dec(v_declName_2402_);
return v___x_2415_;
}
}
else
{
lean_dec_ref(v___f_2410_);
lean_dec_ref(v_value_2404_);
lean_dec(v_declName_2402_);
lean_dec_ref(v_fvars_2393_);
lean_dec_ref(v_postApp_2392_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2387_);
return v___x_2412_;
}
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_expr_instantiate_rev(v_e_2394_, v_fvars_2393_);
lean_dec_ref(v_e_2394_);
lean_inc_ref(v_postApp_2392_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2387_);
v___x_2420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2387_, v_post_2388_, v_usedLetOnly_2389_, v_skipConstInApp_2390_, v_skipInstances_2391_, v_postApp_2392_, v___x_2419_, v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; uint8_t v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = 0;
v___x_2423_ = 1;
v___x_2424_ = l_Lean_Meta_mkLetFVars(v_fvars_2393_, v_a_2421_, v_usedLetOnly_2389_, v___x_2422_, v___x_2423_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec_ref(v_fvars_2393_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2387_, v_post_2388_, v_usedLetOnly_2389_, v_skipConstInApp_2390_, v_skipInstances_2391_, v_postApp_2392_, v_a_2425_, v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2426_;
}
else
{
lean_dec_ref(v_postApp_2392_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2387_);
return v___x_2424_;
}
}
else
{
lean_dec_ref(v_fvars_2393_);
lean_dec_ref(v_postApp_2392_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2387_);
return v___x_2420_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2427_; lean_object* v_dummy_2428_; 
v___x_2427_ = lean_box(0);
v_dummy_2428_ = l_Lean_Expr_sort___override(v___x_2427_);
return v_dummy_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2429_, lean_object* v_post_2430_, uint8_t v_usedLetOnly_2431_, uint8_t v_skipConstInApp_2432_, uint8_t v_skipInstances_2433_, lean_object* v_postApp_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_bs_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v_postApp_2434_);
lean_dec_ref(v_post_2430_);
lean_dec_ref(v_pre_2429_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_bs_2437_);
return v___x_2446_;
}
else
{
lean_object* v_v_2447_; lean_object* v___x_2448_; lean_object* v_bs_x27_2449_; lean_object* v___x_2450_; 
v_v_2447_ = lean_array_uget(v_bs_2437_, v_i_2436_);
v___x_2448_ = lean_unsigned_to_nat(0u);
v_bs_x27_2449_ = lean_array_uset(v_bs_2437_, v_i_2436_, v___x_2448_);
lean_inc_ref(v_postApp_2434_);
lean_inc_ref(v_post_2430_);
lean_inc_ref(v_pre_2429_);
v___x_2450_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2429_, v_post_2430_, v_usedLetOnly_2431_, v_skipConstInApp_2432_, v_skipInstances_2433_, v_postApp_2434_, v_v_2447_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_add(v_i_2436_, v___x_2452_);
v___x_2454_ = lean_array_uset(v_bs_x27_2449_, v_i_2436_, v_a_2451_);
v_i_2436_ = v___x_2453_;
v_bs_2437_ = v___x_2454_;
goto _start;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_bs_x27_2449_);
lean_dec_ref(v_postApp_2434_);
lean_dec_ref(v_post_2430_);
lean_dec_ref(v_pre_2429_);
v_a_2456_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2450_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2450_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_pre_2464_, lean_object* v_post_2465_, uint8_t v_usedLetOnly_2466_, uint8_t v_skipConstInApp_2467_, uint8_t v_skipInstances_2468_, lean_object* v_postApp_2469_, lean_object* v___x_2470_, lean_object* v___y_2471_, lean_object* v_b_2472_, lean_object* v_a_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2464_, v_post_2465_, v_usedLetOnly_2466_, v_skipConstInApp_2467_, v_skipInstances_2468_, v_postApp_2469_, v___x_2470_, v___y_2471_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2490_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2490_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2490_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2485_ = lean_array_fset(v_b_2472_, v_a_2473_, v_a_2481_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2486_);
v___x_2488_ = v___x_2483_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_b_2472_);
v_a_2491_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2480_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2480_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2499_, lean_object* v_post_2500_, lean_object* v_usedLetOnly_2501_, lean_object* v_skipConstInApp_2502_, lean_object* v_skipInstances_2503_, lean_object* v_postApp_2504_, lean_object* v___x_2505_, lean_object* v___y_2506_, lean_object* v_b_2507_, lean_object* v_a_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v_usedLetOnly_boxed_2515_; uint8_t v_skipConstInApp_boxed_2516_; uint8_t v_skipInstances_boxed_2517_; lean_object* v_res_2518_; 
v_usedLetOnly_boxed_2515_ = lean_unbox(v_usedLetOnly_2501_);
v_skipConstInApp_boxed_2516_ = lean_unbox(v_skipConstInApp_2502_);
v_skipInstances_boxed_2517_ = lean_unbox(v_skipInstances_2503_);
v_res_2518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0(v_pre_2499_, v_post_2500_, v_usedLetOnly_boxed_2515_, v_skipConstInApp_boxed_2516_, v_skipInstances_boxed_2517_, v_postApp_2504_, v___x_2505_, v___y_2506_, v_b_2507_, v_a_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec(v_a_2508_);
lean_dec(v___y_2506_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_upperBound_2519_, lean_object* v___x_2520_, lean_object* v_pre_2521_, lean_object* v_post_2522_, uint8_t v_usedLetOnly_2523_, uint8_t v_skipConstInApp_2524_, uint8_t v_skipInstances_2525_, lean_object* v_postApp_2526_, lean_object* v_a_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___y_2537_; uint8_t v___x_2560_; 
v___x_2560_ = lean_nat_dec_lt(v_a_2527_, v_upperBound_2519_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_postApp_2526_);
lean_dec_ref(v_post_2522_);
lean_dec_ref(v_pre_2521_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_b_2528_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2562_ = lean_array_fget_borrowed(v_b_2528_, v_a_2527_);
v___x_2563_ = lean_array_get_size(v___x_2520_);
v___x_2564_ = lean_nat_dec_lt(v_a_2527_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; 
lean_inc(v___x_2562_);
v___x_2565_ = lean_box(v_usedLetOnly_2523_);
v___x_2566_ = lean_box(v_skipConstInApp_2524_);
v___x_2567_ = lean_box(v_skipInstances_2525_);
lean_inc(v_a_2527_);
lean_inc(v___y_2529_);
lean_inc_ref(v_postApp_2526_);
lean_inc_ref(v_post_2522_);
lean_inc_ref(v_pre_2521_);
v___f_2568_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2568_, 0, v_pre_2521_);
lean_closure_set(v___f_2568_, 1, v_post_2522_);
lean_closure_set(v___f_2568_, 2, v___x_2565_);
lean_closure_set(v___f_2568_, 3, v___x_2566_);
lean_closure_set(v___f_2568_, 4, v___x_2567_);
lean_closure_set(v___f_2568_, 5, v_postApp_2526_);
lean_closure_set(v___f_2568_, 6, v___x_2562_);
lean_closure_set(v___f_2568_, 7, v___y_2529_);
lean_closure_set(v___f_2568_, 8, v_b_2528_);
lean_closure_set(v___f_2568_, 9, v_a_2527_);
v___y_2537_ = v___f_2568_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2569_; uint8_t v_isInstance_2570_; 
v___x_2569_ = lean_array_fget_borrowed(v___x_2520_, v_a_2527_);
v_isInstance_2570_ = lean_ctor_get_uint8(v___x_2569_, sizeof(void*)*1 + 4);
if (v_isInstance_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; 
lean_inc(v___x_2562_);
v___x_2571_ = lean_box(v_usedLetOnly_2523_);
v___x_2572_ = lean_box(v_skipConstInApp_2524_);
v___x_2573_ = lean_box(v_skipInstances_2525_);
lean_inc(v_a_2527_);
lean_inc(v___y_2529_);
lean_inc_ref(v_postApp_2526_);
lean_inc_ref(v_post_2522_);
lean_inc_ref(v_pre_2521_);
v___f_2574_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2574_, 0, v_pre_2521_);
lean_closure_set(v___f_2574_, 1, v_post_2522_);
lean_closure_set(v___f_2574_, 2, v___x_2571_);
lean_closure_set(v___f_2574_, 3, v___x_2572_);
lean_closure_set(v___f_2574_, 4, v___x_2573_);
lean_closure_set(v___f_2574_, 5, v_postApp_2526_);
lean_closure_set(v___f_2574_, 6, v___x_2562_);
lean_closure_set(v___f_2574_, 7, v___y_2529_);
lean_closure_set(v___f_2574_, 8, v_b_2528_);
lean_closure_set(v___f_2574_, 9, v_a_2527_);
v___y_2537_ = v___f_2574_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2575_; lean_object* v___f_2576_; 
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2528_);
v___f_2576_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2576_, 0, v___x_2575_);
v___y_2537_ = v___f_2576_;
goto v___jp_2536_;
}
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; 
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
v___x_2538_ = lean_apply_6(v___y_2537_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2551_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
if (lean_obj_tag(v_a_2539_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_postApp_2526_);
lean_dec_ref(v_post_2522_);
lean_dec_ref(v_pre_2521_);
v_a_2543_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v_a_2539_, 1);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v_a_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_del_object(v___x_2541_);
v_a_2547_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v_a_2539_, 1);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_a_2527_, v___x_2548_);
lean_dec(v_a_2527_);
v_a_2527_ = v___x_2549_;
v_b_2528_ = v_a_2547_;
goto _start;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_a_2527_);
lean_dec_ref(v_postApp_2526_);
lean_dec_ref(v_post_2522_);
lean_dec_ref(v_pre_2521_);
v_a_2552_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2538_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2538_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2577_, lean_object* v_pre_2578_, lean_object* v_post_2579_, uint8_t v_usedLetOnly_2580_, uint8_t v_skipConstInApp_2581_, lean_object* v_postApp_2582_, lean_object* v___y_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_f_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; 
if (lean_obj_tag(v_x_2584_) == 5)
{
lean_object* v_fn_2648_; lean_object* v_arg_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_fn_2648_ = lean_ctor_get(v_x_2584_, 0);
lean_inc_ref(v_fn_2648_);
v_arg_2649_ = lean_ctor_get(v_x_2584_, 1);
lean_inc_ref(v_arg_2649_);
lean_dec_ref_known(v_x_2584_, 2);
v___x_2650_ = lean_array_set(v_x_2585_, v_x_2586_, v_arg_2649_);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_nat_sub(v_x_2586_, v___x_2651_);
lean_dec(v_x_2586_);
v_x_2584_ = v_fn_2648_;
v_x_2585_ = v___x_2650_;
v_x_2586_ = v___x_2652_;
goto _start;
}
else
{
lean_dec(v_x_2586_);
if (v_skipConstInApp_2581_ == 0)
{
goto v___jp_2645_;
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_Expr_isConst(v_x_2584_);
if (v___x_2654_ == 0)
{
goto v___jp_2645_;
}
else
{
v_f_2595_ = v_x_2584_;
v___y_2596_ = v___y_2587_;
v___y_2597_ = v___y_2588_;
v___y_2598_ = v___y_2589_;
v___y_2599_ = v___y_2590_;
v___y_2600_ = v___y_2591_;
v___y_2601_ = v___y_2592_;
goto v___jp_2594_;
}
}
}
v___jp_2594_:
{
if (v_skipInstances_2577_ == 0)
{
size_t v_sz_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v_sz_2602_ = lean_array_size(v_x_2585_);
v___x_2603_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_2582_);
lean_inc_ref(v_post_2579_);
lean_inc_ref(v_pre_2578_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2578_, v_post_2579_, v_usedLetOnly_2580_, v_skipConstInApp_2581_, v_skipInstances_2577_, v_postApp_2582_, v_sz_2602_, v___x_2603_, v_x_2585_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = l_Lean_mkAppN(v_f_2595_, v_a_2605_);
lean_dec(v_a_2605_);
lean_inc_ref(v_postApp_2582_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
v___x_2607_ = lean_apply_8(v_postApp_2582_, v___y_2583_, v___x_2606_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, lean_box(0));
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2578_, v_post_2579_, v_usedLetOnly_2580_, v_skipConstInApp_2581_, v_skipInstances_2577_, v_postApp_2582_, v_a_2608_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2609_;
}
else
{
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
return v___x_2607_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v_f_2595_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
v_a_2610_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2604_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2604_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_array_get_size(v_x_2585_);
lean_inc_ref(v_f_2595_);
v___x_2619_ = l_Lean_Meta_getFunInfoNArgs(v_f_2595_, v___x_2618_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v_paramInfo_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v_paramInfo_2621_ = lean_ctor_get(v_a_2620_, 0);
lean_inc_ref(v_paramInfo_2621_);
lean_dec(v_a_2620_);
v___x_2622_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_2582_);
lean_inc_ref(v_post_2579_);
lean_inc_ref(v_pre_2578_);
v___x_2623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v___x_2618_, v_paramInfo_2621_, v_pre_2578_, v_post_2579_, v_usedLetOnly_2580_, v_skipConstInApp_2581_, v_skipInstances_2577_, v_postApp_2582_, v___x_2622_, v_x_2585_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec_ref(v_paramInfo_2621_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = l_Lean_mkAppN(v_f_2595_, v_a_2624_);
lean_dec(v_a_2624_);
lean_inc_ref(v_postApp_2582_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc(v___y_2599_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
v___x_2626_ = lean_apply_8(v_postApp_2582_, v___y_2583_, v___x_2625_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, lean_box(0));
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2578_, v_post_2579_, v_usedLetOnly_2580_, v_skipConstInApp_2581_, v_skipInstances_2577_, v_postApp_2582_, v_a_2627_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2628_;
}
else
{
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
return v___x_2626_;
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v_f_2595_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
v_a_2629_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2623_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2623_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_f_2595_);
lean_dec_ref(v_x_2585_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
v_a_2637_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2619_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2619_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2646_; 
lean_inc_ref(v_postApp_2582_);
lean_inc_ref(v_post_2579_);
lean_inc_ref(v_pre_2578_);
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2578_, v_post_2579_, v_usedLetOnly_2580_, v_skipConstInApp_2581_, v_skipInstances_2577_, v_postApp_2582_, v_x_2584_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v_f_2595_ = v_a_2647_;
v___y_2596_ = v___y_2587_;
v___y_2597_ = v___y_2588_;
v___y_2598_ = v___y_2589_;
v___y_2599_ = v___y_2590_;
v___y_2600_ = v___y_2591_;
v___y_2601_ = v___y_2592_;
goto v___jp_2594_;
}
else
{
lean_dec_ref(v_x_2585_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_postApp_2582_);
lean_dec_ref(v_post_2579_);
lean_dec_ref(v_pre_2578_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2655_, lean_object* v_pre_2656_, lean_object* v_e_2657_, lean_object* v_post_2658_, uint8_t v_usedLetOnly_2659_, uint8_t v_skipConstInApp_2660_, uint8_t v_skipInstances_2661_, lean_object* v_postApp_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Core_checkSystem(v___x_2655_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref_known(v___x_2670_, 1);
lean_inc_ref(v_pre_2656_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v_e_2657_);
v___x_2671_ = lean_apply_7(v_pre_2656_, v_e_2657_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, lean_box(0));
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2720_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2720_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2720_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___y_2677_; 
switch(lean_obj_tag(v_a_2672_))
{
case 0:
{
lean_object* v_e_2712_; lean_object* v___x_2714_; 
lean_dec_ref(v_postApp_2662_);
lean_dec_ref(v_post_2658_);
lean_dec_ref(v_e_2657_);
lean_dec_ref(v_pre_2656_);
v_e_2712_ = lean_ctor_get(v_a_2672_, 0);
lean_inc_ref(v_e_2712_);
lean_dec_ref_known(v_a_2672_, 1);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v_e_2712_);
v___x_2714_ = v___x_2674_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_e_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
case 1:
{
lean_object* v_e_2716_; lean_object* v___x_2717_; 
lean_del_object(v___x_2674_);
lean_dec_ref(v_e_2657_);
v_e_2716_ = lean_ctor_get(v_a_2672_, 0);
lean_inc_ref(v_e_2716_);
lean_dec_ref_known(v_a_2672_, 1);
v___x_2717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v_e_2716_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2717_;
}
default: 
{
lean_object* v_e_x3f_2718_; 
lean_del_object(v___x_2674_);
v_e_x3f_2718_ = lean_ctor_get(v_a_2672_, 0);
lean_inc(v_e_x3f_2718_);
lean_dec_ref_known(v_a_2672_, 1);
if (lean_obj_tag(v_e_x3f_2718_) == 0)
{
v___y_2677_ = v_e_2657_;
goto v___jp_2676_;
}
else
{
lean_object* v_val_2719_; 
lean_dec_ref(v_e_2657_);
v_val_2719_ = lean_ctor_get(v_e_x3f_2718_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v_e_x3f_2718_, 1);
v___y_2677_ = v_val_2719_;
goto v___jp_2676_;
}
}
}
v___jp_2676_:
{
switch(lean_obj_tag(v___y_2677_))
{
case 7:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2679_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___x_2678_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2679_;
}
case 6:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___x_2680_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2681_;
}
case 8:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___x_2682_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2683_;
}
case 5:
{
lean_object* v_dummy_2684_; lean_object* v_nargs_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_dummy_2684_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2685_ = l_Lean_Expr_getAppNumArgs(v___y_2677_);
lean_inc(v_nargs_2685_);
v___x_2686_ = lean_mk_array(v_nargs_2685_, v_dummy_2684_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_sub(v_nargs_2685_, v___x_2687_);
lean_dec(v_nargs_2685_);
lean_inc_ref(v___y_2677_);
v___x_2689_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2661_, v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_postApp_2662_, v___y_2677_, v___y_2677_, v___x_2686_, v___x_2688_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2689_;
}
case 10:
{
lean_object* v_data_2690_; lean_object* v_expr_2691_; lean_object* v___x_2692_; 
v_data_2690_ = lean_ctor_get(v___y_2677_, 0);
v_expr_2691_ = lean_ctor_get(v___y_2677_, 1);
lean_inc_ref(v_expr_2691_);
lean_inc_ref(v_postApp_2662_);
lean_inc_ref(v_post_2658_);
lean_inc_ref(v_pre_2656_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v_expr_2691_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; size_t v___x_2694_; size_t v___x_2695_; uint8_t v___x_2696_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = lean_ptr_addr(v_expr_2691_);
v___x_2695_ = lean_ptr_addr(v_a_2693_);
v___x_2696_ = lean_usize_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc(v_data_2690_);
lean_dec_ref_known(v___y_2677_, 2);
v___x_2697_ = l_Lean_Expr_mdata___override(v_data_2690_, v_a_2693_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___x_2697_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_a_2693_);
v___x_2699_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2699_;
}
}
else
{
lean_dec_ref_known(v___y_2677_, 2);
lean_dec_ref(v_postApp_2662_);
lean_dec_ref(v_post_2658_);
lean_dec_ref(v_pre_2656_);
return v___x_2692_;
}
}
case 11:
{
lean_object* v_typeName_2700_; lean_object* v_idx_2701_; lean_object* v_struct_2702_; lean_object* v___x_2703_; 
v_typeName_2700_ = lean_ctor_get(v___y_2677_, 0);
v_idx_2701_ = lean_ctor_get(v___y_2677_, 1);
v_struct_2702_ = lean_ctor_get(v___y_2677_, 2);
lean_inc_ref(v_struct_2702_);
lean_inc_ref(v_postApp_2662_);
lean_inc_ref(v_post_2658_);
lean_inc_ref(v_pre_2656_);
v___x_2703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v_struct_2702_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; size_t v___x_2705_; size_t v___x_2706_; uint8_t v___x_2707_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_ptr_addr(v_struct_2702_);
v___x_2706_ = lean_ptr_addr(v_a_2704_);
v___x_2707_ = lean_usize_dec_eq(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc(v_idx_2701_);
lean_inc(v_typeName_2700_);
lean_dec_ref_known(v___y_2677_, 3);
v___x_2708_ = l_Lean_Expr_proj___override(v_typeName_2700_, v_idx_2701_, v_a_2704_);
v___x_2709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___x_2708_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2709_;
}
else
{
lean_object* v___x_2710_; 
lean_dec(v_a_2704_);
v___x_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2710_;
}
}
else
{
lean_dec_ref_known(v___y_2677_, 3);
lean_dec_ref(v_postApp_2662_);
lean_dec_ref(v_post_2658_);
lean_dec_ref(v_pre_2656_);
return v___x_2703_;
}
}
default: 
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2656_, v_post_2658_, v_usedLetOnly_2659_, v_skipConstInApp_2660_, v_skipInstances_2661_, v_postApp_2662_, v___y_2677_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2711_;
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_postApp_2662_);
lean_dec_ref(v_post_2658_);
lean_dec_ref(v_e_2657_);
lean_dec_ref(v_pre_2656_);
v_a_2721_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2671_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2671_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_postApp_2662_);
lean_dec_ref(v_post_2658_);
lean_dec_ref(v_e_2657_);
lean_dec_ref(v_pre_2656_);
v_a_2729_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2670_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2670_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2737_, lean_object* v_pre_2738_, lean_object* v_e_2739_, lean_object* v_post_2740_, lean_object* v_usedLetOnly_2741_, lean_object* v_skipConstInApp_2742_, lean_object* v_skipInstances_2743_, lean_object* v_postApp_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v_usedLetOnly_boxed_2752_; uint8_t v_skipConstInApp_boxed_2753_; uint8_t v_skipInstances_boxed_2754_; lean_object* v_res_2755_; 
v_usedLetOnly_boxed_2752_ = lean_unbox(v_usedLetOnly_2741_);
v_skipConstInApp_boxed_2753_ = lean_unbox(v_skipConstInApp_2742_);
v_skipInstances_boxed_2754_ = lean_unbox(v_skipInstances_2743_);
v_res_2755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2737_, v_pre_2738_, v_e_2739_, v_post_2740_, v_usedLetOnly_boxed_2752_, v_skipConstInApp_boxed_2753_, v_skipInstances_boxed_2754_, v_postApp_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2756_, lean_object* v_post_2757_, uint8_t v_usedLetOnly_2758_, uint8_t v_skipConstInApp_2759_, uint8_t v_skipInstances_2760_, lean_object* v_postApp_2761_, lean_object* v_e_2762_, lean_object* v_a_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_inc(v_a_2763_);
v___x_2770_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2770_, 0, lean_box(0));
lean_closure_set(v___x_2770_, 1, lean_box(0));
lean_closure_set(v___x_2770_, 2, v_a_2763_);
v___x_2771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2770_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2806_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2806_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2806_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg(v_a_2772_, v_e_2762_);
lean_dec(v_a_2772_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
lean_del_object(v___x_2774_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2778_ = lean_box(v_usedLetOnly_2758_);
v___x_2779_ = lean_box(v_skipConstInApp_2759_);
v___x_2780_ = lean_box(v_skipInstances_2760_);
lean_inc_ref(v_e_2762_);
v___f_2781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 15, 8);
lean_closure_set(v___f_2781_, 0, v___x_2777_);
lean_closure_set(v___f_2781_, 1, v_pre_2756_);
lean_closure_set(v___f_2781_, 2, v_e_2762_);
lean_closure_set(v___f_2781_, 3, v_post_2757_);
lean_closure_set(v___f_2781_, 4, v___x_2778_);
lean_closure_set(v___f_2781_, 5, v___x_2779_);
lean_closure_set(v___f_2781_, 6, v___x_2780_);
lean_closure_set(v___f_2781_, 7, v_postApp_2761_);
v___x_2782_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2781_, v_a_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc_n(v_a_2783_, 2);
lean_dec_ref_known(v___x_2782_, 1);
lean_inc(v_a_2763_);
v___f_2784_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2784_, 0, v_a_2763_);
lean_closure_set(v___f_2784_, 1, v_e_2762_);
lean_closure_set(v___f_2784_, 2, v_a_2783_);
v___x_2785_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2784_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v___x_2785_, 0);
lean_dec(v_unused_2793_);
v___x_2787_ = v___x_2785_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_dec(v___x_2785_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_a_2783_);
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2783_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_a_2783_);
v_a_2794_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2785_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2785_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_dec_ref(v_e_2762_);
return v___x_2782_;
}
}
else
{
lean_object* v_val_2802_; lean_object* v___x_2804_; 
lean_dec_ref(v_e_2762_);
lean_dec_ref(v_postApp_2761_);
lean_dec_ref(v_post_2757_);
lean_dec_ref(v_pre_2756_);
v_val_2802_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_val_2802_);
lean_dec_ref_known(v___x_2776_, 1);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v_val_2802_);
v___x_2804_ = v___x_2774_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_val_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v_e_2762_);
lean_dec_ref(v_postApp_2761_);
lean_dec_ref(v_post_2757_);
lean_dec_ref(v_pre_2756_);
v_a_2807_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2771_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2771_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2815_, lean_object* v_post_2816_, uint8_t v_usedLetOnly_2817_, uint8_t v_skipConstInApp_2818_, uint8_t v_skipInstances_2819_, lean_object* v_postApp_2820_, lean_object* v_fvars_2821_, lean_object* v_e_2822_, lean_object* v_a_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
if (lean_obj_tag(v_e_2822_) == 7)
{
lean_object* v_binderName_2830_; lean_object* v_binderType_2831_; lean_object* v_body_2832_; uint8_t v_binderInfo_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_binderName_2830_ = lean_ctor_get(v_e_2822_, 0);
lean_inc(v_binderName_2830_);
v_binderType_2831_ = lean_ctor_get(v_e_2822_, 1);
lean_inc_ref(v_binderType_2831_);
v_body_2832_ = lean_ctor_get(v_e_2822_, 2);
lean_inc_ref(v_body_2832_);
v_binderInfo_2833_ = lean_ctor_get_uint8(v_e_2822_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2822_, 3);
v___x_2834_ = lean_box(v_usedLetOnly_2817_);
v___x_2835_ = lean_box(v_skipConstInApp_2818_);
v___x_2836_ = lean_box(v_skipInstances_2819_);
lean_inc_ref(v_postApp_2820_);
lean_inc_ref(v_post_2816_);
lean_inc_ref(v_pre_2815_);
lean_inc_ref(v_fvars_2821_);
v___f_2837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2837_, 0, v_fvars_2821_);
lean_closure_set(v___f_2837_, 1, v_pre_2815_);
lean_closure_set(v___f_2837_, 2, v_post_2816_);
lean_closure_set(v___f_2837_, 3, v___x_2834_);
lean_closure_set(v___f_2837_, 4, v___x_2835_);
lean_closure_set(v___f_2837_, 5, v___x_2836_);
lean_closure_set(v___f_2837_, 6, v_postApp_2820_);
lean_closure_set(v___f_2837_, 7, v_body_2832_);
v___x_2838_ = lean_expr_instantiate_rev(v_binderType_2831_, v_fvars_2821_);
lean_dec_ref(v_fvars_2821_);
lean_dec_ref(v_binderType_2831_);
v___x_2839_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v_postApp_2820_, v___x_2838_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = 0;
v___x_2842_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2830_, v_binderInfo_2833_, v_a_2840_, v___f_2837_, v___x_2841_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2842_;
}
else
{
lean_dec_ref(v___f_2837_);
lean_dec(v_binderName_2830_);
return v___x_2839_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_expr_instantiate_rev(v_e_2822_, v_fvars_2821_);
lean_dec_ref(v_e_2822_);
lean_inc_ref(v_postApp_2820_);
lean_inc_ref(v_post_2816_);
lean_inc_ref(v_pre_2815_);
v___x_2844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v_postApp_2820_, v___x_2843_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; uint8_t v___x_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = 0;
v___x_2847_ = 1;
v___x_2848_ = 1;
v___x_2849_ = l_Lean_Meta_mkForallFVars(v_fvars_2821_, v_a_2845_, v___x_2846_, v_usedLetOnly_2817_, v___x_2847_, v___x_2848_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref(v_fvars_2821_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v_postApp_2820_, v_a_2850_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2851_;
}
else
{
lean_dec_ref(v_postApp_2820_);
lean_dec_ref(v_post_2816_);
lean_dec_ref(v_pre_2815_);
return v___x_2849_;
}
}
else
{
lean_dec_ref(v_fvars_2821_);
lean_dec_ref(v_postApp_2820_);
lean_dec_ref(v_post_2816_);
lean_dec_ref(v_pre_2815_);
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2852_, lean_object* v_pre_2853_, lean_object* v_post_2854_, uint8_t v_usedLetOnly_2855_, uint8_t v_skipConstInApp_2856_, uint8_t v_skipInstances_2857_, lean_object* v_postApp_2858_, lean_object* v_body_2859_, lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_array_push(v_fvars_2852_, v_x_2860_);
v___x_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2853_, v_post_2854_, v_usedLetOnly_2855_, v_skipConstInApp_2856_, v_skipInstances_2857_, v_postApp_2858_, v___x_2868_, v_body_2859_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_2870_, lean_object* v_post_2871_, lean_object* v_usedLetOnly_2872_, lean_object* v_skipConstInApp_2873_, lean_object* v_skipInstances_2874_, lean_object* v_postApp_2875_, lean_object* v_e_2876_, lean_object* v_a_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v_usedLetOnly_boxed_2884_; uint8_t v_skipConstInApp_boxed_2885_; uint8_t v_skipInstances_boxed_2886_; lean_object* v_res_2887_; 
v_usedLetOnly_boxed_2884_ = lean_unbox(v_usedLetOnly_2872_);
v_skipConstInApp_boxed_2885_ = lean_unbox(v_skipConstInApp_2873_);
v_skipInstances_boxed_2886_ = lean_unbox(v_skipInstances_2874_);
v_res_2887_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_pre_2870_, v_post_2871_, v_usedLetOnly_boxed_2884_, v_skipConstInApp_boxed_2885_, v_skipInstances_boxed_2886_, v_postApp_2875_, v_e_2876_, v_a_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v_a_2877_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2888_, lean_object* v_post_2889_, lean_object* v_usedLetOnly_2890_, lean_object* v_skipConstInApp_2891_, lean_object* v_skipInstances_2892_, lean_object* v_postApp_2893_, lean_object* v_sz_2894_, lean_object* v_i_2895_, lean_object* v_bs_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
uint8_t v_usedLetOnly_boxed_2904_; uint8_t v_skipConstInApp_boxed_2905_; uint8_t v_skipInstances_boxed_2906_; size_t v_sz_boxed_2907_; size_t v_i_boxed_2908_; lean_object* v_res_2909_; 
v_usedLetOnly_boxed_2904_ = lean_unbox(v_usedLetOnly_2890_);
v_skipConstInApp_boxed_2905_ = lean_unbox(v_skipConstInApp_2891_);
v_skipInstances_boxed_2906_ = lean_unbox(v_skipInstances_2892_);
v_sz_boxed_2907_ = lean_unbox_usize(v_sz_2894_);
lean_dec(v_sz_2894_);
v_i_boxed_2908_ = lean_unbox_usize(v_i_2895_);
lean_dec(v_i_2895_);
v_res_2909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2888_, v_post_2889_, v_usedLetOnly_boxed_2904_, v_skipConstInApp_boxed_2905_, v_skipInstances_boxed_2906_, v_postApp_2893_, v_sz_boxed_2907_, v_i_boxed_2908_, v_bs_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec(v___y_2897_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2910_, lean_object* v_post_2911_, lean_object* v_usedLetOnly_2912_, lean_object* v_skipConstInApp_2913_, lean_object* v_skipInstances_2914_, lean_object* v_postApp_2915_, lean_object* v_e_2916_, lean_object* v_a_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
uint8_t v_usedLetOnly_boxed_2924_; uint8_t v_skipConstInApp_boxed_2925_; uint8_t v_skipInstances_boxed_2926_; lean_object* v_res_2927_; 
v_usedLetOnly_boxed_2924_ = lean_unbox(v_usedLetOnly_2912_);
v_skipConstInApp_boxed_2925_ = lean_unbox(v_skipConstInApp_2913_);
v_skipInstances_boxed_2926_ = lean_unbox(v_skipInstances_2914_);
v_res_2927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2910_, v_post_2911_, v_usedLetOnly_boxed_2924_, v_skipConstInApp_boxed_2925_, v_skipInstances_boxed_2926_, v_postApp_2915_, v_e_2916_, v_a_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v_a_2917_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2928_, lean_object* v_post_2929_, lean_object* v_usedLetOnly_2930_, lean_object* v_skipConstInApp_2931_, lean_object* v_skipInstances_2932_, lean_object* v_postApp_2933_, lean_object* v_fvars_2934_, lean_object* v_e_2935_, lean_object* v_a_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
uint8_t v_usedLetOnly_boxed_2943_; uint8_t v_skipConstInApp_boxed_2944_; uint8_t v_skipInstances_boxed_2945_; lean_object* v_res_2946_; 
v_usedLetOnly_boxed_2943_ = lean_unbox(v_usedLetOnly_2930_);
v_skipConstInApp_boxed_2944_ = lean_unbox(v_skipConstInApp_2931_);
v_skipInstances_boxed_2945_ = lean_unbox(v_skipInstances_2932_);
v_res_2946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2928_, v_post_2929_, v_usedLetOnly_boxed_2943_, v_skipConstInApp_boxed_2944_, v_skipInstances_boxed_2945_, v_postApp_2933_, v_fvars_2934_, v_e_2935_, v_a_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v_a_2936_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2947_, lean_object* v_post_2948_, lean_object* v_usedLetOnly_2949_, lean_object* v_skipConstInApp_2950_, lean_object* v_skipInstances_2951_, lean_object* v_postApp_2952_, lean_object* v_fvars_2953_, lean_object* v_e_2954_, lean_object* v_a_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v_usedLetOnly_boxed_2962_; uint8_t v_skipConstInApp_boxed_2963_; uint8_t v_skipInstances_boxed_2964_; lean_object* v_res_2965_; 
v_usedLetOnly_boxed_2962_ = lean_unbox(v_usedLetOnly_2949_);
v_skipConstInApp_boxed_2963_ = lean_unbox(v_skipConstInApp_2950_);
v_skipInstances_boxed_2964_ = lean_unbox(v_skipInstances_2951_);
v_res_2965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2947_, v_post_2948_, v_usedLetOnly_boxed_2962_, v_skipConstInApp_boxed_2963_, v_skipInstances_boxed_2964_, v_postApp_2952_, v_fvars_2953_, v_e_2954_, v_a_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v_a_2955_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2966_, lean_object* v_post_2967_, lean_object* v_usedLetOnly_2968_, lean_object* v_skipConstInApp_2969_, lean_object* v_skipInstances_2970_, lean_object* v_postApp_2971_, lean_object* v_fvars_2972_, lean_object* v_e_2973_, lean_object* v_a_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v_usedLetOnly_boxed_2981_; uint8_t v_skipConstInApp_boxed_2982_; uint8_t v_skipInstances_boxed_2983_; lean_object* v_res_2984_; 
v_usedLetOnly_boxed_2981_ = lean_unbox(v_usedLetOnly_2968_);
v_skipConstInApp_boxed_2982_ = lean_unbox(v_skipConstInApp_2969_);
v_skipInstances_boxed_2983_ = lean_unbox(v_skipInstances_2970_);
v_res_2984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2966_, v_post_2967_, v_usedLetOnly_boxed_2981_, v_skipConstInApp_boxed_2982_, v_skipInstances_boxed_2983_, v_postApp_2971_, v_fvars_2972_, v_e_2973_, v_a_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec(v_a_2974_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2985_ = _args[0];
lean_object* v___x_2986_ = _args[1];
lean_object* v_pre_2987_ = _args[2];
lean_object* v_post_2988_ = _args[3];
lean_object* v_usedLetOnly_2989_ = _args[4];
lean_object* v_skipConstInApp_2990_ = _args[5];
lean_object* v_skipInstances_2991_ = _args[6];
lean_object* v_postApp_2992_ = _args[7];
lean_object* v_a_2993_ = _args[8];
lean_object* v_b_2994_ = _args[9];
lean_object* v___y_2995_ = _args[10];
lean_object* v___y_2996_ = _args[11];
lean_object* v___y_2997_ = _args[12];
lean_object* v___y_2998_ = _args[13];
lean_object* v___y_2999_ = _args[14];
lean_object* v___y_3000_ = _args[15];
lean_object* v___y_3001_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_3002_; uint8_t v_skipConstInApp_boxed_3003_; uint8_t v_skipInstances_boxed_3004_; lean_object* v_res_3005_; 
v_usedLetOnly_boxed_3002_ = lean_unbox(v_usedLetOnly_2989_);
v_skipConstInApp_boxed_3003_ = lean_unbox(v_skipConstInApp_2990_);
v_skipInstances_boxed_3004_ = lean_unbox(v_skipInstances_2991_);
v_res_3005_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_upperBound_2985_, v___x_2986_, v_pre_2987_, v_post_2988_, v_usedLetOnly_boxed_3002_, v_skipConstInApp_boxed_3003_, v_skipInstances_boxed_3004_, v_postApp_2992_, v_a_2993_, v_b_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___x_2986_);
lean_dec(v_upperBound_2985_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object** _args){
lean_object* v_skipInstances_3006_ = _args[0];
lean_object* v_pre_3007_ = _args[1];
lean_object* v_post_3008_ = _args[2];
lean_object* v_usedLetOnly_3009_ = _args[3];
lean_object* v_skipConstInApp_3010_ = _args[4];
lean_object* v_postApp_3011_ = _args[5];
lean_object* v___y_3012_ = _args[6];
lean_object* v_x_3013_ = _args[7];
lean_object* v_x_3014_ = _args[8];
lean_object* v_x_3015_ = _args[9];
lean_object* v___y_3016_ = _args[10];
lean_object* v___y_3017_ = _args[11];
lean_object* v___y_3018_ = _args[12];
lean_object* v___y_3019_ = _args[13];
lean_object* v___y_3020_ = _args[14];
lean_object* v___y_3021_ = _args[15];
lean_object* v___y_3022_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_3023_; uint8_t v_usedLetOnly_boxed_3024_; uint8_t v_skipConstInApp_boxed_3025_; lean_object* v_res_3026_; 
v_skipInstances_boxed_3023_ = lean_unbox(v_skipInstances_3006_);
v_usedLetOnly_boxed_3024_ = lean_unbox(v_usedLetOnly_3009_);
v_skipConstInApp_boxed_3025_ = lean_unbox(v_skipConstInApp_3010_);
v_res_3026_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3023_, v_pre_3007_, v_post_3008_, v_usedLetOnly_boxed_3024_, v_skipConstInApp_boxed_3025_, v_postApp_3011_, v___y_3012_, v_x_3013_, v_x_3014_, v_x_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec(v___y_3016_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1(lean_object* v_x_3027_, lean_object* v_e_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_e_3028_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1___boxed(lean_object* v_x_3036_, lean_object* v_e_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__1(v_x_3036_, v_e_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v_x_3036_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3045_, lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_apply_1(v_x_3046_, lean_box(0));
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3055_, v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
return v_res_3063_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_unsigned_to_nat(16u);
v___x_3067_ = lean_mk_array(v___x_3066_, v___x_3065_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3072_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3072_, 0, lean_box(0));
lean_closure_set(v___x_3072_, 1, lean_box(0));
lean_closure_set(v___x_3072_, 2, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3073_, lean_object* v_pre_3074_, lean_object* v_post_3075_, uint8_t v_usedLetOnly_3076_, uint8_t v_skipConstInApp_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___f_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_a_3088_; lean_object* v___x_3089_; 
v___f_3084_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0));
v___x_3085_ = 0;
v___x_3086_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3);
v___x_3087_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3086_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref(v___x_3087_);
v___x_3089_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3074_, v_post_3075_, v_usedLetOnly_3076_, v_skipConstInApp_3077_, v___x_3085_, v___f_3084_, v_input_3073_, v_a_3088_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3091_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3091_, 0, lean_box(0));
lean_closure_set(v___x_3091_, 1, lean_box(0));
lean_closure_set(v___x_3091_, 2, v_a_3088_);
v___x_3092_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3091_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3092_, 0);
lean_dec(v_unused_3100_);
v___x_3094_ = v___x_3092_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v___x_3092_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_a_3090_);
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3090_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_dec(v_a_3088_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3101_, lean_object* v_pre_3102_, lean_object* v_post_3103_, lean_object* v_usedLetOnly_3104_, lean_object* v_skipConstInApp_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
uint8_t v_usedLetOnly_boxed_3112_; uint8_t v_skipConstInApp_boxed_3113_; lean_object* v_res_3114_; 
v_usedLetOnly_boxed_3112_ = lean_unbox(v_usedLetOnly_3104_);
v_skipConstInApp_boxed_3113_ = lean_unbox(v_skipConstInApp_3105_);
v_res_3114_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3101_, v_pre_3102_, v_post_3103_, v_usedLetOnly_boxed_3112_, v_skipConstInApp_boxed_3113_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3116_, uint8_t v_elimTrivial_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; lean_object* v_pre_3124_; lean_object* v___f_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3123_ = lean_box(v_elimTrivial_3117_);
v_pre_3124_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3124_, 0, v___x_3123_);
v___f_3125_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3126_ = 0;
v___x_3127_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_3128_ = lean_st_mk_ref(v___x_3127_);
v___x_3129_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3116_, v_pre_3124_, v___f_3125_, v___x_3126_, v___x_3126_, v___x_3128_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3138_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_st_ref_get(v___x_3128_);
lean_dec(v___x_3128_);
lean_dec(v___x_3134_);
if (v_isShared_3133_ == 0)
{
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3130_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_dec(v___x_3128_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3139_, lean_object* v_elimTrivial_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
uint8_t v_elimTrivial_boxed_3146_; lean_object* v_res_3147_; 
v_elimTrivial_boxed_3146_ = lean_unbox(v_elimTrivial_3140_);
v_res_3147_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3139_, v_elimTrivial_boxed_3146_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3148_, lean_object* v_m_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___redArg(v_m_3149_, v_a_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3152_, lean_object* v_m_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_00_u03b2_3152_, v_m_3153_, v_a_3154_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_m_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_upperBound_3156_, lean_object* v___x_3157_, lean_object* v_pre_3158_, lean_object* v_post_3159_, uint8_t v_usedLetOnly_3160_, uint8_t v_skipConstInApp_3161_, uint8_t v_skipInstances_3162_, lean_object* v_postApp_3163_, lean_object* v___x_3164_, lean_object* v_inst_3165_, lean_object* v_R_3166_, lean_object* v_a_3167_, lean_object* v_b_3168_, lean_object* v_c_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_upperBound_3156_, v___x_3157_, v_pre_3158_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_postApp_3163_, v_a_3167_, v_b_3168_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3178_ = _args[0];
lean_object* v___x_3179_ = _args[1];
lean_object* v_pre_3180_ = _args[2];
lean_object* v_post_3181_ = _args[3];
lean_object* v_usedLetOnly_3182_ = _args[4];
lean_object* v_skipConstInApp_3183_ = _args[5];
lean_object* v_skipInstances_3184_ = _args[6];
lean_object* v_postApp_3185_ = _args[7];
lean_object* v___x_3186_ = _args[8];
lean_object* v_inst_3187_ = _args[9];
lean_object* v_R_3188_ = _args[10];
lean_object* v_a_3189_ = _args[11];
lean_object* v_b_3190_ = _args[12];
lean_object* v_c_3191_ = _args[13];
lean_object* v___y_3192_ = _args[14];
lean_object* v___y_3193_ = _args[15];
lean_object* v___y_3194_ = _args[16];
lean_object* v___y_3195_ = _args[17];
lean_object* v___y_3196_ = _args[18];
lean_object* v___y_3197_ = _args[19];
lean_object* v___y_3198_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_3199_; uint8_t v_skipConstInApp_boxed_3200_; uint8_t v_skipInstances_boxed_3201_; lean_object* v_res_3202_; 
v_usedLetOnly_boxed_3199_ = lean_unbox(v_usedLetOnly_3182_);
v_skipConstInApp_boxed_3200_ = lean_unbox(v_skipConstInApp_3183_);
v_skipInstances_boxed_3201_ = lean_unbox(v_skipInstances_3184_);
v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_upperBound_3178_, v___x_3179_, v_pre_3180_, v_post_3181_, v_usedLetOnly_boxed_3199_, v_skipConstInApp_boxed_3200_, v_skipInstances_boxed_3201_, v_postApp_3185_, v___x_3186_, v_inst_3187_, v_R_3188_, v_a_3189_, v_b_3190_, v_c_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec(v___x_3186_);
lean_dec_ref(v___x_3179_);
lean_dec(v_upperBound_3178_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3203_, lean_object* v_name_3204_, uint8_t v_bi_3205_, lean_object* v_type_3206_, lean_object* v_k_3207_, uint8_t v_kind_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3204_, v_bi_3205_, v_type_3206_, v_k_3207_, v_kind_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_name_3218_, lean_object* v_bi_3219_, lean_object* v_type_3220_, lean_object* v_k_3221_, lean_object* v_kind_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
uint8_t v_bi_boxed_3230_; uint8_t v_kind_boxed_3231_; lean_object* v_res_3232_; 
v_bi_boxed_3230_ = lean_unbox(v_bi_3219_);
v_kind_boxed_3231_ = lean_unbox(v_kind_3222_);
v_res_3232_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3217_, v_name_3218_, v_bi_boxed_3230_, v_type_3220_, v_k_3221_, v_kind_boxed_3231_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec(v___y_3223_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3233_, lean_object* v_name_3234_, lean_object* v_type_3235_, lean_object* v_val_3236_, lean_object* v_k_3237_, uint8_t v_nondep_3238_, uint8_t v_kind_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3234_, v_type_3235_, v_val_3236_, v_k_3237_, v_nondep_3238_, v_kind_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3248_, lean_object* v_name_3249_, lean_object* v_type_3250_, lean_object* v_val_3251_, lean_object* v_k_3252_, lean_object* v_nondep_3253_, lean_object* v_kind_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v_nondep_boxed_3262_; uint8_t v_kind_boxed_3263_; lean_object* v_res_3264_; 
v_nondep_boxed_3262_ = lean_unbox(v_nondep_3253_);
v_kind_boxed_3263_ = lean_unbox(v_kind_3254_);
v_res_3264_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3248_, v_name_3249_, v_type_3250_, v_val_3251_, v_k_3252_, v_nondep_boxed_3262_, v_kind_boxed_3263_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3265_, lean_object* v_ref_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3266_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_ref_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3273_, v_ref_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3291_, v_x_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3301_, lean_object* v_m_3302_, lean_object* v_a_3303_, lean_object* v_b_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3302_, v_a_3303_, v_b_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3306_, lean_object* v_a_3307_, lean_object* v_x_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3307_, v_x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3310_, lean_object* v_a_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_3310_, v_a_3311_, v_x_3312_);
lean_dec(v_x_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3314_, lean_object* v_a_3315_, lean_object* v_x_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3315_, v_x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_a_3319_, lean_object* v_x_3320_){
_start:
{
uint8_t v_res_3321_; lean_object* v_r_3322_; 
v_res_3321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3318_, v_a_3319_, v_x_3320_);
lean_dec(v_x_3320_);
lean_dec_ref(v_a_3319_);
v_r_3322_ = lean_box(v_res_3321_);
return v_r_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3323_, lean_object* v_data_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3326_, lean_object* v_a_3327_, lean_object* v_b_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3327_, v_b_3328_, v_x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3331_, lean_object* v_i_3332_, lean_object* v_source_3333_, lean_object* v_target_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3332_, v_source_3333_, v_target_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3337_, v_x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3340_, v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
v_a_3356_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3347_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3347_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3364_, lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3364_, v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3372_, lean_object* v_mvarId_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3381_, lean_object* v_mvarId_3382_, lean_object* v_x_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3381_, v_mvarId_3382_, v_x_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3390_, lean_object* v_as_3391_, size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_b_3394_){
_start:
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_b_3394_);
return v___x_3397_;
}
else
{
lean_object* v_snd_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3445_; 
v_snd_3398_ = lean_ctor_get(v_b_3394_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_b_3394_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v_b_3394_, 0);
lean_dec(v_unused_3446_);
v___x_3400_ = v_b_3394_;
v_isShared_3401_ = v_isSharedCheck_3445_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_snd_3398_);
lean_dec(v_b_3394_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3445_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v_a_3404_; lean_object* v_a_3411_; 
v___x_3402_ = lean_box(0);
v_a_3411_ = lean_array_uget_borrowed(v_as_3391_, v_i_3393_);
if (lean_obj_tag(v_a_3411_) == 0)
{
v_a_3404_ = v_snd_3398_;
goto v___jp_3403_;
}
else
{
lean_object* v_val_3412_; lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3444_; 
v_val_3412_ = lean_ctor_get(v_a_3411_, 0);
v_fst_3413_ = lean_ctor_get(v_snd_3398_, 0);
v_snd_3414_ = lean_ctor_get(v_snd_3398_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_snd_3398_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3416_ = v_snd_3398_;
v_isShared_3417_ = v_isSharedCheck_3444_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_snd_3414_);
lean_inc(v_fst_3413_);
lean_dec(v_snd_3398_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3444_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
uint8_t v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = 0;
v___x_3419_ = l_Lean_LocalDecl_value_x3f(v_val_3412_, v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 1)
{
lean_object* v_val_3420_; lean_object* v___x_3421_; 
v_val_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_val_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = l_Lean_LocalDecl_type(v_val_3412_);
if (lean_obj_tag(v___x_3421_) == 10)
{
lean_object* v_data_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; uint8_t v___x_3427_; 
v_data_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_data_3422_);
lean_dec_ref_known(v___x_3421_, 2);
v___x_3423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3424_ = lean_unsigned_to_nat(2u);
v___x_3425_ = l_Lean_KVMap_getNat(v_data_3422_, v___x_3423_, v___x_3424_);
lean_dec(v_data_3422_);
v___x_3426_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3425_);
lean_dec(v___x_3425_);
v___x_3427_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3426_, v_val_3420_, v_elimTrivial_3390_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3428_ = l_Lean_LocalDecl_fvarId(v_val_3412_);
v___x_3429_ = l_Lean_mkFVar(v___x_3428_);
v___x_3430_ = lean_array_push(v_fst_3413_, v___x_3429_);
v___x_3431_ = lean_array_push(v_snd_3414_, v_val_3420_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v___x_3431_);
lean_ctor_set(v___x_3416_, 0, v___x_3430_);
v___x_3433_ = v___x_3416_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3430_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
v_a_3404_ = v___x_3433_;
goto v___jp_3403_;
}
}
else
{
lean_object* v___x_3436_; 
lean_dec(v_val_3420_);
if (v_isShared_3417_ == 0)
{
v___x_3436_ = v___x_3416_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_fst_3413_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_snd_3414_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
v_a_3404_ = v___x_3436_;
goto v___jp_3403_;
}
}
}
else
{
lean_object* v___x_3439_; 
lean_dec_ref(v___x_3421_);
lean_dec(v_val_3420_);
if (v_isShared_3417_ == 0)
{
v___x_3439_ = v___x_3416_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_fst_3413_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_snd_3414_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
v_a_3404_ = v___x_3439_;
goto v___jp_3403_;
}
}
}
else
{
lean_object* v___x_3442_; 
lean_dec(v___x_3419_);
if (v_isShared_3417_ == 0)
{
v___x_3442_ = v___x_3416_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_fst_3413_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_snd_3414_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v_a_3404_ = v___x_3442_;
goto v___jp_3403_;
}
}
}
}
v___jp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v_a_3404_);
lean_ctor_set(v___x_3400_, 0, v___x_3402_);
v___x_3406_ = v___x_3400_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_a_3404_);
v___x_3406_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
size_t v___x_3407_; size_t v___x_3408_; 
v___x_3407_ = ((size_t)1ULL);
v___x_3408_ = lean_usize_add(v_i_3393_, v___x_3407_);
v_i_3393_ = v___x_3408_;
v_b_3394_ = v___x_3406_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3447_, lean_object* v_as_3448_, lean_object* v_sz_3449_, lean_object* v_i_3450_, lean_object* v_b_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_elimTrivial_boxed_3453_; size_t v_sz_boxed_3454_; size_t v_i_boxed_3455_; lean_object* v_res_3456_; 
v_elimTrivial_boxed_3453_ = lean_unbox(v_elimTrivial_3447_);
v_sz_boxed_3454_ = lean_unbox_usize(v_sz_3449_);
lean_dec(v_sz_3449_);
v_i_boxed_3455_ = lean_unbox_usize(v_i_3450_);
lean_dec(v_i_3450_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3453_, v_as_3448_, v_sz_boxed_3454_, v_i_boxed_3455_, v_b_3451_);
lean_dec_ref(v_as_3448_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3457_, lean_object* v_as_3458_, size_t v_sz_3459_, size_t v_i_3460_, lean_object* v_b_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_usize_dec_lt(v_i_3460_, v_sz_3459_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_b_3461_);
return v___x_3468_;
}
else
{
lean_object* v_snd_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3516_; 
v_snd_3469_ = lean_ctor_get(v_b_3461_, 1);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_b_3461_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; 
v_unused_3517_ = lean_ctor_get(v_b_3461_, 0);
lean_dec(v_unused_3517_);
v___x_3471_ = v_b_3461_;
v_isShared_3472_ = v_isSharedCheck_3516_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_snd_3469_);
lean_dec(v_b_3461_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3516_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_a_3475_; lean_object* v_a_3482_; 
v___x_3473_ = lean_box(0);
v_a_3482_ = lean_array_uget_borrowed(v_as_3458_, v_i_3460_);
if (lean_obj_tag(v_a_3482_) == 0)
{
v_a_3475_ = v_snd_3469_;
goto v___jp_3474_;
}
else
{
lean_object* v_val_3483_; lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3515_; 
v_val_3483_ = lean_ctor_get(v_a_3482_, 0);
v_fst_3484_ = lean_ctor_get(v_snd_3469_, 0);
v_snd_3485_ = lean_ctor_get(v_snd_3469_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_snd_3469_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3487_ = v_snd_3469_;
v_isShared_3488_ = v_isSharedCheck_3515_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_snd_3485_);
lean_inc(v_fst_3484_);
lean_dec(v_snd_3469_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3515_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
uint8_t v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = 0;
v___x_3490_ = l_Lean_LocalDecl_value_x3f(v_val_3483_, v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3492_; 
v_val_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = l_Lean_LocalDecl_type(v_val_3483_);
if (lean_obj_tag(v___x_3492_) == 10)
{
lean_object* v_data_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; uint8_t v___x_3498_; 
v_data_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_data_3493_);
lean_dec_ref_known(v___x_3492_, 2);
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3495_ = lean_unsigned_to_nat(2u);
v___x_3496_ = l_Lean_KVMap_getNat(v_data_3493_, v___x_3494_, v___x_3495_);
lean_dec(v_data_3493_);
v___x_3497_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3496_);
lean_dec(v___x_3496_);
v___x_3498_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3497_, v_val_3491_, v_elimTrivial_3457_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3499_ = l_Lean_LocalDecl_fvarId(v_val_3483_);
v___x_3500_ = l_Lean_mkFVar(v___x_3499_);
v___x_3501_ = lean_array_push(v_fst_3484_, v___x_3500_);
v___x_3502_ = lean_array_push(v_snd_3485_, v_val_3491_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3502_);
lean_ctor_set(v___x_3487_, 0, v___x_3501_);
v___x_3504_ = v___x_3487_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
v_a_3475_ = v___x_3504_;
goto v___jp_3474_;
}
}
else
{
lean_object* v___x_3507_; 
lean_dec(v_val_3491_);
if (v_isShared_3488_ == 0)
{
v___x_3507_ = v___x_3487_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_snd_3485_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v_a_3475_ = v___x_3507_;
goto v___jp_3474_;
}
}
}
else
{
lean_object* v___x_3510_; 
lean_dec_ref(v___x_3492_);
lean_dec(v_val_3491_);
if (v_isShared_3488_ == 0)
{
v___x_3510_ = v___x_3487_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_snd_3485_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
v_a_3475_ = v___x_3510_;
goto v___jp_3474_;
}
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v___x_3490_);
if (v_isShared_3488_ == 0)
{
v___x_3513_ = v___x_3487_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_fst_3484_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_snd_3485_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
v_a_3475_ = v___x_3513_;
goto v___jp_3474_;
}
}
}
}
v___jp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v_a_3475_);
lean_ctor_set(v___x_3471_, 0, v___x_3473_);
v___x_3477_ = v___x_3471_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3475_);
v___x_3477_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)1ULL);
v___x_3479_ = lean_usize_add(v_i_3460_, v___x_3478_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3457_, v_as_3458_, v_sz_3459_, v___x_3479_, v___x_3477_);
return v___x_3480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3518_, lean_object* v_as_3519_, lean_object* v_sz_3520_, lean_object* v_i_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
uint8_t v_elimTrivial_boxed_3528_; size_t v_sz_boxed_3529_; size_t v_i_boxed_3530_; lean_object* v_res_3531_; 
v_elimTrivial_boxed_3528_ = lean_unbox(v_elimTrivial_3518_);
v_sz_boxed_3529_ = lean_unbox_usize(v_sz_3520_);
lean_dec(v_sz_3520_);
v_i_boxed_3530_ = lean_unbox_usize(v_i_3521_);
lean_dec(v_i_3521_);
v_res_3531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3528_, v_as_3519_, v_sz_boxed_3529_, v_i_boxed_3530_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v_as_3519_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3532_, lean_object* v_as_3533_, size_t v_sz_3534_, size_t v_i_3535_, lean_object* v_b_3536_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_lt(v_i_3535_, v_sz_3534_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_b_3536_);
return v___x_3539_;
}
else
{
lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3587_; 
v_snd_3540_ = lean_ctor_get(v_b_3536_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_b_3536_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v_b_3536_, 0);
lean_dec(v_unused_3588_);
v___x_3542_ = v_b_3536_;
v_isShared_3543_ = v_isSharedCheck_3587_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_dec(v_b_3536_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3587_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v_a_3546_; lean_object* v_a_3553_; 
v___x_3544_ = lean_box(0);
v_a_3553_ = lean_array_uget_borrowed(v_as_3533_, v_i_3535_);
if (lean_obj_tag(v_a_3553_) == 0)
{
v_a_3546_ = v_snd_3540_;
goto v___jp_3545_;
}
else
{
lean_object* v_val_3554_; lean_object* v_fst_3555_; lean_object* v_snd_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3586_; 
v_val_3554_ = lean_ctor_get(v_a_3553_, 0);
v_fst_3555_ = lean_ctor_get(v_snd_3540_, 0);
v_snd_3556_ = lean_ctor_get(v_snd_3540_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_snd_3540_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3558_ = v_snd_3540_;
v_isShared_3559_ = v_isSharedCheck_3586_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_snd_3556_);
lean_inc(v_fst_3555_);
lean_dec(v_snd_3540_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3586_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
uint8_t v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = 0;
v___x_3561_ = l_Lean_LocalDecl_value_x3f(v_val_3554_, v___x_3560_);
if (lean_obj_tag(v___x_3561_) == 1)
{
lean_object* v_val_3562_; lean_object* v___x_3563_; 
v_val_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_val_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = l_Lean_LocalDecl_type(v_val_3554_);
if (lean_obj_tag(v___x_3563_) == 10)
{
lean_object* v_data_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; uint8_t v___x_3569_; 
v_data_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_data_3564_);
lean_dec_ref_known(v___x_3563_, 2);
v___x_3565_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3566_ = lean_unsigned_to_nat(2u);
v___x_3567_ = l_Lean_KVMap_getNat(v_data_3564_, v___x_3565_, v___x_3566_);
lean_dec(v_data_3564_);
v___x_3568_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3567_);
lean_dec(v___x_3567_);
v___x_3569_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3568_, v_val_3562_, v_elimTrivial_3532_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3570_ = l_Lean_LocalDecl_fvarId(v_val_3554_);
v___x_3571_ = l_Lean_mkFVar(v___x_3570_);
v___x_3572_ = lean_array_push(v_fst_3555_, v___x_3571_);
v___x_3573_ = lean_array_push(v_snd_3556_, v_val_3562_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v___x_3573_);
lean_ctor_set(v___x_3558_, 0, v___x_3572_);
v___x_3575_ = v___x_3558_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v_a_3546_ = v___x_3575_;
goto v___jp_3545_;
}
}
else
{
lean_object* v___x_3578_; 
lean_dec(v_val_3562_);
if (v_isShared_3559_ == 0)
{
v___x_3578_ = v___x_3558_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_fst_3555_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_snd_3556_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
v_a_3546_ = v___x_3578_;
goto v___jp_3545_;
}
}
}
else
{
lean_object* v___x_3581_; 
lean_dec_ref(v___x_3563_);
lean_dec(v_val_3562_);
if (v_isShared_3559_ == 0)
{
v___x_3581_ = v___x_3558_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_fst_3555_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_snd_3556_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
v_a_3546_ = v___x_3581_;
goto v___jp_3545_;
}
}
}
else
{
lean_object* v___x_3584_; 
lean_dec(v___x_3561_);
if (v_isShared_3559_ == 0)
{
v___x_3584_ = v___x_3558_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_fst_3555_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_snd_3556_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
v_a_3546_ = v___x_3584_;
goto v___jp_3545_;
}
}
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_a_3546_);
lean_ctor_set(v___x_3542_, 0, v___x_3544_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3546_);
v___x_3548_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
size_t v___x_3549_; size_t v___x_3550_; 
v___x_3549_ = ((size_t)1ULL);
v___x_3550_ = lean_usize_add(v_i_3535_, v___x_3549_);
v_i_3535_ = v___x_3550_;
v_b_3536_ = v___x_3548_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3589_, lean_object* v_as_3590_, lean_object* v_sz_3591_, lean_object* v_i_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_){
_start:
{
uint8_t v_elimTrivial_boxed_3595_; size_t v_sz_boxed_3596_; size_t v_i_boxed_3597_; lean_object* v_res_3598_; 
v_elimTrivial_boxed_3595_ = lean_unbox(v_elimTrivial_3589_);
v_sz_boxed_3596_ = lean_unbox_usize(v_sz_3591_);
lean_dec(v_sz_3591_);
v_i_boxed_3597_ = lean_unbox_usize(v_i_3592_);
lean_dec(v_i_3592_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3595_, v_as_3590_, v_sz_boxed_3596_, v_i_boxed_3597_, v_b_3593_);
lean_dec_ref(v_as_3590_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3599_, lean_object* v_as_3600_, size_t v_sz_3601_, size_t v_i_3602_, lean_object* v_b_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_usize_dec_lt(v_i_3602_, v_sz_3601_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_b_3603_);
return v___x_3610_;
}
else
{
lean_object* v_snd_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3658_; 
v_snd_3611_ = lean_ctor_get(v_b_3603_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_b_3603_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v_b_3603_, 0);
lean_dec(v_unused_3659_);
v___x_3613_ = v_b_3603_;
v_isShared_3614_ = v_isSharedCheck_3658_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_snd_3611_);
lean_dec(v_b_3603_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3658_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v_a_3617_; lean_object* v_a_3624_; 
v___x_3615_ = lean_box(0);
v_a_3624_ = lean_array_uget_borrowed(v_as_3600_, v_i_3602_);
if (lean_obj_tag(v_a_3624_) == 0)
{
v_a_3617_ = v_snd_3611_;
goto v___jp_3616_;
}
else
{
lean_object* v_val_3625_; lean_object* v_fst_3626_; lean_object* v_snd_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3657_; 
v_val_3625_ = lean_ctor_get(v_a_3624_, 0);
v_fst_3626_ = lean_ctor_get(v_snd_3611_, 0);
v_snd_3627_ = lean_ctor_get(v_snd_3611_, 1);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_snd_3611_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3629_ = v_snd_3611_;
v_isShared_3630_ = v_isSharedCheck_3657_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_snd_3627_);
lean_inc(v_fst_3626_);
lean_dec(v_snd_3611_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3657_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
uint8_t v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = 0;
v___x_3632_ = l_Lean_LocalDecl_value_x3f(v_val_3625_, v___x_3631_);
if (lean_obj_tag(v___x_3632_) == 1)
{
lean_object* v_val_3633_; lean_object* v___x_3634_; 
v_val_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_val_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_LocalDecl_type(v_val_3625_);
if (lean_obj_tag(v___x_3634_) == 10)
{
lean_object* v_data_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; uint8_t v___x_3640_; 
v_data_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_data_3635_);
lean_dec_ref_known(v___x_3634_, 2);
v___x_3636_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3637_ = lean_unsigned_to_nat(2u);
v___x_3638_ = l_Lean_KVMap_getNat(v_data_3635_, v___x_3636_, v___x_3637_);
lean_dec(v_data_3635_);
v___x_3639_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3638_);
lean_dec(v___x_3638_);
v___x_3640_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3639_, v_val_3633_, v_elimTrivial_3599_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3641_ = l_Lean_LocalDecl_fvarId(v_val_3625_);
v___x_3642_ = l_Lean_mkFVar(v___x_3641_);
v___x_3643_ = lean_array_push(v_fst_3626_, v___x_3642_);
v___x_3644_ = lean_array_push(v_snd_3627_, v_val_3633_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 1, v___x_3644_);
lean_ctor_set(v___x_3629_, 0, v___x_3643_);
v___x_3646_ = v___x_3629_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
v_a_3617_ = v___x_3646_;
goto v___jp_3616_;
}
}
else
{
lean_object* v___x_3649_; 
lean_dec(v_val_3633_);
if (v_isShared_3630_ == 0)
{
v___x_3649_ = v___x_3629_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_fst_3626_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_snd_3627_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
v_a_3617_ = v___x_3649_;
goto v___jp_3616_;
}
}
}
else
{
lean_object* v___x_3652_; 
lean_dec_ref(v___x_3634_);
lean_dec(v_val_3633_);
if (v_isShared_3630_ == 0)
{
v___x_3652_ = v___x_3629_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_fst_3626_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_snd_3627_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
v_a_3617_ = v___x_3652_;
goto v___jp_3616_;
}
}
}
else
{
lean_object* v___x_3655_; 
lean_dec(v___x_3632_);
if (v_isShared_3630_ == 0)
{
v___x_3655_ = v___x_3629_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_fst_3626_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_snd_3627_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
v_a_3617_ = v___x_3655_;
goto v___jp_3616_;
}
}
}
}
v___jp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v_a_3617_);
lean_ctor_set(v___x_3613_, 0, v___x_3615_);
v___x_3619_ = v___x_3613_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_a_3617_);
v___x_3619_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = ((size_t)1ULL);
v___x_3621_ = lean_usize_add(v_i_3602_, v___x_3620_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3599_, v_as_3600_, v_sz_3601_, v___x_3621_, v___x_3619_);
return v___x_3622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3660_, lean_object* v_as_3661_, lean_object* v_sz_3662_, lean_object* v_i_3663_, lean_object* v_b_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_elimTrivial_boxed_3670_; size_t v_sz_boxed_3671_; size_t v_i_boxed_3672_; lean_object* v_res_3673_; 
v_elimTrivial_boxed_3670_ = lean_unbox(v_elimTrivial_3660_);
v_sz_boxed_3671_ = lean_unbox_usize(v_sz_3662_);
lean_dec(v_sz_3662_);
v_i_boxed_3672_ = lean_unbox_usize(v_i_3663_);
lean_dec(v_i_3663_);
v_res_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3670_, v_as_3661_, v_sz_boxed_3671_, v_i_boxed_3672_, v_b_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec_ref(v_as_3661_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3674_, uint8_t v_elimTrivial_3675_, lean_object* v_n_3676_, lean_object* v_b_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
if (lean_obj_tag(v_n_3676_) == 0)
{
lean_object* v_cs_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; size_t v_sz_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v_cs_3683_ = lean_ctor_get(v_n_3676_, 0);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_b_3677_);
v_sz_3686_ = lean_array_size(v_cs_3683_);
v___x_3687_ = ((size_t)0ULL);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3674_, v_elimTrivial_3675_, v_cs_3683_, v_sz_3686_, v___x_3687_, v___x_3685_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3703_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3703_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3703_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_fst_3693_; 
v_fst_3693_ = lean_ctor_get(v_a_3689_, 0);
if (lean_obj_tag(v_fst_3693_) == 0)
{
lean_object* v_snd_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
v_snd_3694_ = lean_ctor_get(v_a_3689_, 1);
lean_inc(v_snd_3694_);
lean_dec(v_a_3689_);
v___x_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3695_, 0, v_snd_3694_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3695_);
v___x_3697_ = v___x_3691_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
else
{
lean_object* v_val_3699_; lean_object* v___x_3701_; 
lean_inc_ref(v_fst_3693_);
lean_dec(v_a_3689_);
v_val_3699_ = lean_ctor_get(v_fst_3693_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v_fst_3693_, 1);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v_val_3699_);
v___x_3701_ = v___x_3691_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_val_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
v_a_3704_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3688_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3688_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_vs_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; size_t v_sz_3715_; size_t v___x_3716_; lean_object* v___x_3717_; 
v_vs_3712_ = lean_ctor_get(v_n_3676_, 0);
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v_b_3677_);
v_sz_3715_ = lean_array_size(v_vs_3712_);
v___x_3716_ = ((size_t)0ULL);
v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3675_, v_vs_3712_, v_sz_3715_, v___x_3716_, v___x_3714_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3732_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3732_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_fst_3722_; 
v_fst_3722_ = lean_ctor_get(v_a_3718_, 0);
if (lean_obj_tag(v_fst_3722_) == 0)
{
lean_object* v_snd_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v_snd_3723_ = lean_ctor_get(v_a_3718_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_a_3718_);
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_snd_3723_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3724_);
v___x_3726_ = v___x_3720_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3730_; 
lean_inc_ref(v_fst_3722_);
lean_dec(v_a_3718_);
v_val_3728_ = lean_ctor_get(v_fst_3722_, 0);
lean_inc(v_val_3728_);
lean_dec_ref_known(v_fst_3722_, 1);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_val_3728_);
v___x_3730_ = v___x_3720_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_val_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v_a_3733_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3717_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3717_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3741_, uint8_t v_elimTrivial_3742_, lean_object* v_as_3743_, size_t v_sz_3744_, size_t v_i_3745_, lean_object* v_b_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v___x_3752_; 
v___x_3752_ = lean_usize_dec_lt(v_i_3745_, v_sz_3744_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_b_3746_);
return v___x_3753_;
}
else
{
lean_object* v_snd_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3788_; 
v_snd_3754_ = lean_ctor_get(v_b_3746_, 1);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_b_3746_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; 
v_unused_3789_ = lean_ctor_get(v_b_3746_, 0);
lean_dec(v_unused_3789_);
v___x_3756_ = v_b_3746_;
v_isShared_3757_ = v_isSharedCheck_3788_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_snd_3754_);
lean_dec(v_b_3746_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3788_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_box(0);
v_a_3759_ = lean_array_uget_borrowed(v_as_3743_, v_i_3745_);
lean_inc(v_snd_3754_);
v___x_3760_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3741_, v_elimTrivial_3742_, v_a_3759_, v_snd_3754_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3779_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3779_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
if (lean_obj_tag(v_a_3761_) == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v_a_3761_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v___x_3765_);
v___x_3767_ = v___x_3756_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_snd_3754_);
v___x_3767_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3769_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3767_);
v___x_3769_ = v___x_3763_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; 
lean_del_object(v___x_3763_);
lean_dec(v_snd_3754_);
v_a_3772_ = lean_ctor_get(v_a_3761_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v_a_3761_, 1);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v_a_3772_);
lean_ctor_set(v___x_3756_, 0, v___x_3758_);
v___x_3774_ = v___x_3756_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_a_3772_);
v___x_3774_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
size_t v___x_3775_; size_t v___x_3776_; 
v___x_3775_ = ((size_t)1ULL);
v___x_3776_ = lean_usize_add(v_i_3745_, v___x_3775_);
v_i_3745_ = v___x_3776_;
v_b_3746_ = v___x_3774_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_del_object(v___x_3756_);
lean_dec(v_snd_3754_);
v_a_3780_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3760_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3760_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3790_, lean_object* v_elimTrivial_3791_, lean_object* v_as_3792_, lean_object* v_sz_3793_, lean_object* v_i_3794_, lean_object* v_b_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
uint8_t v_elimTrivial_boxed_3801_; size_t v_sz_boxed_3802_; size_t v_i_boxed_3803_; lean_object* v_res_3804_; 
v_elimTrivial_boxed_3801_ = lean_unbox(v_elimTrivial_3791_);
v_sz_boxed_3802_ = lean_unbox_usize(v_sz_3793_);
lean_dec(v_sz_3793_);
v_i_boxed_3803_ = lean_unbox_usize(v_i_3794_);
lean_dec(v_i_3794_);
v_res_3804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3790_, v_elimTrivial_boxed_3801_, v_as_3792_, v_sz_boxed_3802_, v_i_boxed_3803_, v_b_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v_as_3792_);
lean_dec_ref(v_init_3790_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3805_, lean_object* v_elimTrivial_3806_, lean_object* v_n_3807_, lean_object* v_b_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v_elimTrivial_boxed_3814_; lean_object* v_res_3815_; 
v_elimTrivial_boxed_3814_ = lean_unbox(v_elimTrivial_3806_);
v_res_3815_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3805_, v_elimTrivial_boxed_3814_, v_n_3807_, v_b_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_n_3807_);
lean_dec_ref(v_init_3805_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3816_, lean_object* v_t_3817_, lean_object* v_init_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_root_3824_; lean_object* v_tail_3825_; lean_object* v___x_3826_; 
v_root_3824_ = lean_ctor_get(v_t_3817_, 0);
v_tail_3825_ = lean_ctor_get(v_t_3817_, 1);
lean_inc_ref(v_init_3818_);
v___x_3826_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3818_, v_elimTrivial_3816_, v_root_3824_, v_init_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec_ref(v_init_3818_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3863_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3829_ = v___x_3826_;
v_isShared_3830_ = v_isSharedCheck_3863_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3863_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
if (lean_obj_tag(v_a_3827_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; 
v_a_3831_ = lean_ctor_get(v_a_3827_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v_a_3827_, 1);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v_a_3831_);
v___x_3833_ = v___x_3829_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; size_t v_sz_3838_; size_t v___x_3839_; lean_object* v___x_3840_; 
lean_del_object(v___x_3829_);
v_a_3835_ = lean_ctor_get(v_a_3827_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v_a_3827_, 1);
v___x_3836_ = lean_box(0);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
lean_ctor_set(v___x_3837_, 1, v_a_3835_);
v_sz_3838_ = lean_array_size(v_tail_3825_);
v___x_3839_ = ((size_t)0ULL);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3816_, v_tail_3825_, v_sz_3838_, v___x_3839_, v___x_3837_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3854_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3854_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3854_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v_fst_3845_; 
v_fst_3845_ = lean_ctor_get(v_a_3841_, 0);
if (lean_obj_tag(v_fst_3845_) == 0)
{
lean_object* v_snd_3846_; lean_object* v___x_3848_; 
v_snd_3846_ = lean_ctor_get(v_a_3841_, 1);
lean_inc(v_snd_3846_);
lean_dec(v_a_3841_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v_snd_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_snd_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
else
{
lean_object* v_val_3850_; lean_object* v___x_3852_; 
lean_inc_ref(v_fst_3845_);
lean_dec(v_a_3841_);
v_val_3850_ = lean_ctor_get(v_fst_3845_, 0);
lean_inc(v_val_3850_);
lean_dec_ref_known(v_fst_3845_, 1);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v_val_3850_);
v___x_3852_ = v___x_3843_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_val_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v_a_3855_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3840_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3840_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3864_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3826_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3826_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3872_, lean_object* v_t_3873_, lean_object* v_init_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
uint8_t v_elimTrivial_boxed_3880_; lean_object* v_res_3881_; 
v_elimTrivial_boxed_3880_ = lean_unbox(v_elimTrivial_3872_);
v_res_3881_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3880_, v_t_3873_, v_init_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v_t_3873_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3882_, size_t v_sz_3883_, size_t v_i_3884_, lean_object* v_b_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_usize_dec_lt(v_i_3884_, v_sz_3883_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_b_3885_);
return v___x_3892_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_a_3893_ = lean_array_uget_borrowed(v_as_3882_, v_i_3884_);
v___x_3894_ = l_Lean_Expr_fvarId_x21(v_a_3893_);
v___x_3895_ = l_Lean_MVarId_tryClear(v_b_3885_, v___x_3894_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; size_t v___x_3897_; size_t v___x_3898_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_add(v_i_3884_, v___x_3897_);
v_i_3884_ = v___x_3898_;
v_b_3885_ = v_a_3896_;
goto _start;
}
else
{
return v___x_3895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3900_, lean_object* v_sz_3901_, lean_object* v_i_3902_, lean_object* v_b_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
size_t v_sz_boxed_3909_; size_t v_i_boxed_3910_; lean_object* v_res_3911_; 
v_sz_boxed_3909_ = lean_unbox_usize(v_sz_3901_);
lean_dec(v_sz_3901_);
v_i_boxed_3910_ = lean_unbox_usize(v_i_3902_);
lean_dec(v_i_3902_);
v_res_3911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3900_, v_sz_boxed_3909_, v_i_boxed_3910_, v_b_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v_as_3900_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_){
_start:
{
lean_object* v_ks_3916_; lean_object* v_vs_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3941_; 
v_ks_3916_ = lean_ctor_get(v_x_3912_, 0);
v_vs_3917_ = lean_ctor_get(v_x_3912_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_x_3912_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3919_ = v_x_3912_;
v_isShared_3920_ = v_isSharedCheck_3941_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_vs_3917_);
lean_inc(v_ks_3916_);
lean_dec(v_x_3912_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3941_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3921_ = lean_array_get_size(v_ks_3916_);
v___x_3922_ = lean_nat_dec_lt(v_x_3913_, v___x_3921_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec(v_x_3913_);
v___x_3923_ = lean_array_push(v_ks_3916_, v_x_3914_);
v___x_3924_ = lean_array_push(v_vs_3917_, v_x_3915_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 1, v___x_3924_);
lean_ctor_set(v___x_3919_, 0, v___x_3923_);
v___x_3926_ = v___x_3919_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
else
{
lean_object* v_k_x27_3928_; uint8_t v___x_3929_; 
v_k_x27_3928_ = lean_array_fget_borrowed(v_ks_3916_, v_x_3913_);
v___x_3929_ = l_Lean_instBEqMVarId_beq(v_x_3914_, v_k_x27_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3931_; 
if (v_isShared_3920_ == 0)
{
v___x_3931_ = v___x_3919_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_ks_3916_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_vs_3917_);
v___x_3931_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_unsigned_to_nat(1u);
v___x_3933_ = lean_nat_add(v_x_3913_, v___x_3932_);
lean_dec(v_x_3913_);
v_x_3912_ = v___x_3931_;
v_x_3913_ = v___x_3933_;
goto _start;
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3936_ = lean_array_fset(v_ks_3916_, v_x_3913_, v_x_3914_);
v___x_3937_ = lean_array_fset(v_vs_3917_, v_x_3913_, v_x_3915_);
lean_dec(v_x_3913_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 1, v___x_3937_);
lean_ctor_set(v___x_3919_, 0, v___x_3936_);
v___x_3939_ = v___x_3919_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3942_, lean_object* v_k_3943_, lean_object* v_v_3944_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_unsigned_to_nat(0u);
v___x_3946_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3942_, v___x_3945_, v_k_3943_, v_v_3944_);
return v___x_3946_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3948_, size_t v_x_3949_, size_t v_x_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_){
_start:
{
if (lean_obj_tag(v_x_3948_) == 0)
{
lean_object* v_es_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v_j_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_es_3953_ = lean_ctor_get(v_x_3948_, 0);
v___x_3954_ = ((size_t)31ULL);
v___x_3955_ = lean_usize_land(v_x_3949_, v___x_3954_);
v_j_3956_ = lean_usize_to_nat(v___x_3955_);
v___x_3957_ = lean_array_get_size(v_es_3953_);
v___x_3958_ = lean_nat_dec_lt(v_j_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_dec(v_j_3956_);
lean_dec(v_x_3952_);
lean_dec(v_x_3951_);
return v_x_3948_;
}
else
{
lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3997_; 
lean_inc_ref(v_es_3953_);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_x_3948_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; 
v_unused_3998_ = lean_ctor_get(v_x_3948_, 0);
lean_dec(v_unused_3998_);
v___x_3960_ = v_x_3948_;
v_isShared_3961_ = v_isSharedCheck_3997_;
goto v_resetjp_3959_;
}
else
{
lean_dec(v_x_3948_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3997_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_v_3962_; lean_object* v___x_3963_; lean_object* v_xs_x27_3964_; lean_object* v___y_3966_; 
v_v_3962_ = lean_array_fget(v_es_3953_, v_j_3956_);
v___x_3963_ = lean_box(0);
v_xs_x27_3964_ = lean_array_fset(v_es_3953_, v_j_3956_, v___x_3963_);
switch(lean_obj_tag(v_v_3962_))
{
case 0:
{
lean_object* v_key_3971_; lean_object* v_val_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3982_; 
v_key_3971_ = lean_ctor_get(v_v_3962_, 0);
v_val_3972_ = lean_ctor_get(v_v_3962_, 1);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_v_3962_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3974_ = v_v_3962_;
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_val_3972_);
lean_inc(v_key_3971_);
lean_dec(v_v_3962_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3982_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
uint8_t v___x_3976_; 
v___x_3976_ = l_Lean_instBEqMVarId_beq(v_x_3951_, v_key_3971_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_del_object(v___x_3974_);
v___x_3977_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3971_, v_val_3972_, v_x_3951_, v_x_3952_);
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
v___y_3966_ = v___x_3978_;
goto v___jp_3965_;
}
else
{
lean_object* v___x_3980_; 
lean_dec(v_val_3972_);
lean_dec(v_key_3971_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v_x_3952_);
lean_ctor_set(v___x_3974_, 0, v_x_3951_);
v___x_3980_ = v___x_3974_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_x_3951_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_x_3952_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
v___y_3966_ = v___x_3980_;
goto v___jp_3965_;
}
}
}
}
case 1:
{
lean_object* v_node_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3995_; 
v_node_3983_ = lean_ctor_get(v_v_3962_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_v_3962_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3985_ = v_v_3962_;
v_isShared_3986_ = v_isSharedCheck_3995_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_node_3983_);
lean_dec(v_v_3962_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3995_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3987_ = ((size_t)5ULL);
v___x_3988_ = lean_usize_shift_right(v_x_3949_, v___x_3987_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_add(v_x_3950_, v___x_3989_);
v___x_3991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3983_, v___x_3988_, v___x_3990_, v_x_3951_, v_x_3952_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3991_);
v___x_3993_ = v___x_3985_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
v___y_3966_ = v___x_3993_;
goto v___jp_3965_;
}
}
}
default: 
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3996_, 0, v_x_3951_);
lean_ctor_set(v___x_3996_, 1, v_x_3952_);
v___y_3966_ = v___x_3996_;
goto v___jp_3965_;
}
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_array_fset(v_xs_x27_3964_, v_j_3956_, v___y_3966_);
lean_dec(v_j_3956_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3967_);
v___x_3969_ = v___x_3960_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v_ks_3999_; lean_object* v_vs_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4018_; 
v_ks_3999_ = lean_ctor_get(v_x_3948_, 0);
v_vs_4000_ = lean_ctor_get(v_x_3948_, 1);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_x_3948_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4002_ = v_x_3948_;
v_isShared_4003_ = v_isSharedCheck_4018_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_vs_4000_);
lean_inc(v_ks_3999_);
lean_dec(v_x_3948_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4018_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_ks_3999_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_vs_4000_);
v___x_4005_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v_newNode_4006_; size_t v___x_4007_; uint8_t v___x_4008_; 
v_newNode_4006_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_4005_, v_x_3951_, v_x_3952_);
v___x_4007_ = ((size_t)7ULL);
v___x_4008_ = lean_usize_dec_le(v___x_4007_, v_x_3950_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4009_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4006_);
v___x_4010_ = lean_unsigned_to_nat(4u);
v___x_4011_ = lean_nat_dec_lt(v___x_4009_, v___x_4010_);
lean_dec(v___x_4009_);
if (v___x_4011_ == 0)
{
lean_object* v_ks_4012_; lean_object* v_vs_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v_ks_4012_ = lean_ctor_get(v_newNode_4006_, 0);
lean_inc_ref(v_ks_4012_);
v_vs_4013_ = lean_ctor_get(v_newNode_4006_, 1);
lean_inc_ref(v_vs_4013_);
lean_dec_ref(v_newNode_4006_);
v___x_4014_ = lean_unsigned_to_nat(0u);
v___x_4015_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_4016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3950_, v_ks_4012_, v_vs_4013_, v___x_4014_, v___x_4015_);
lean_dec_ref(v_vs_4013_);
lean_dec_ref(v_ks_4012_);
return v___x_4016_;
}
else
{
return v_newNode_4006_;
}
}
else
{
return v_newNode_4006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_4019_, lean_object* v_keys_4020_, lean_object* v_vals_4021_, lean_object* v_i_4022_, lean_object* v_entries_4023_){
_start:
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = lean_array_get_size(v_keys_4020_);
v___x_4025_ = lean_nat_dec_lt(v_i_4022_, v___x_4024_);
if (v___x_4025_ == 0)
{
lean_dec(v_i_4022_);
return v_entries_4023_;
}
else
{
lean_object* v_k_4026_; lean_object* v_v_4027_; uint64_t v___x_4028_; size_t v_h_4029_; size_t v___x_4030_; lean_object* v___x_4031_; size_t v___x_4032_; size_t v___x_4033_; size_t v___x_4034_; size_t v_h_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_k_4026_ = lean_array_fget_borrowed(v_keys_4020_, v_i_4022_);
v_v_4027_ = lean_array_fget_borrowed(v_vals_4021_, v_i_4022_);
v___x_4028_ = l_Lean_instHashableMVarId_hash(v_k_4026_);
v_h_4029_ = lean_uint64_to_usize(v___x_4028_);
v___x_4030_ = ((size_t)5ULL);
v___x_4031_ = lean_unsigned_to_nat(1u);
v___x_4032_ = ((size_t)1ULL);
v___x_4033_ = lean_usize_sub(v_depth_4019_, v___x_4032_);
v___x_4034_ = lean_usize_mul(v___x_4030_, v___x_4033_);
v_h_4035_ = lean_usize_shift_right(v_h_4029_, v___x_4034_);
v___x_4036_ = lean_nat_add(v_i_4022_, v___x_4031_);
lean_dec(v_i_4022_);
lean_inc(v_v_4027_);
lean_inc(v_k_4026_);
v___x_4037_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_4023_, v_h_4035_, v_depth_4019_, v_k_4026_, v_v_4027_);
v_i_4022_ = v___x_4036_;
v_entries_4023_ = v___x_4037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4039_, lean_object* v_keys_4040_, lean_object* v_vals_4041_, lean_object* v_i_4042_, lean_object* v_entries_4043_){
_start:
{
size_t v_depth_boxed_4044_; lean_object* v_res_4045_; 
v_depth_boxed_4044_ = lean_unbox_usize(v_depth_4039_);
lean_dec(v_depth_4039_);
v_res_4045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4044_, v_keys_4040_, v_vals_4041_, v_i_4042_, v_entries_4043_);
lean_dec_ref(v_vals_4041_);
lean_dec_ref(v_keys_4040_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_, lean_object* v_x_4050_){
_start:
{
size_t v_x_7822__boxed_4051_; size_t v_x_7823__boxed_4052_; lean_object* v_res_4053_; 
v_x_7822__boxed_4051_ = lean_unbox_usize(v_x_4047_);
lean_dec(v_x_4047_);
v_x_7823__boxed_4052_ = lean_unbox_usize(v_x_4048_);
lean_dec(v_x_4048_);
v_res_4053_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4046_, v_x_7822__boxed_4051_, v_x_7823__boxed_4052_, v_x_4049_, v_x_4050_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4054_, lean_object* v_x_4055_, lean_object* v_x_4056_){
_start:
{
uint64_t v___x_4057_; size_t v___x_4058_; size_t v___x_4059_; lean_object* v___x_4060_; 
v___x_4057_ = l_Lean_instHashableMVarId_hash(v_x_4055_);
v___x_4058_ = lean_uint64_to_usize(v___x_4057_);
v___x_4059_ = ((size_t)1ULL);
v___x_4060_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4054_, v___x_4058_, v___x_4059_, v_x_4055_, v_x_4056_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4061_, lean_object* v_val_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; lean_object* v_mctx_4066_; lean_object* v_cache_4067_; lean_object* v_zetaDeltaFVarIds_4068_; lean_object* v_postponed_4069_; lean_object* v_diag_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4099_; 
v___x_4065_ = lean_st_ref_take(v___y_4063_);
v_mctx_4066_ = lean_ctor_get(v___x_4065_, 0);
v_cache_4067_ = lean_ctor_get(v___x_4065_, 1);
v_zetaDeltaFVarIds_4068_ = lean_ctor_get(v___x_4065_, 2);
v_postponed_4069_ = lean_ctor_get(v___x_4065_, 3);
v_diag_4070_ = lean_ctor_get(v___x_4065_, 4);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4072_ = v___x_4065_;
v_isShared_4073_ = v_isSharedCheck_4099_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_diag_4070_);
lean_inc(v_postponed_4069_);
lean_inc(v_zetaDeltaFVarIds_4068_);
lean_inc(v_cache_4067_);
lean_inc(v_mctx_4066_);
lean_dec(v___x_4065_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4099_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v_depth_4074_; lean_object* v_levelAssignDepth_4075_; lean_object* v_lmvarCounter_4076_; lean_object* v_mvarCounter_4077_; lean_object* v_lDecls_4078_; lean_object* v_decls_4079_; lean_object* v_userNames_4080_; lean_object* v_lAssignment_4081_; lean_object* v_eAssignment_4082_; lean_object* v_dAssignment_4083_; lean_object* v_synthNormMemo_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4098_; 
v_depth_4074_ = lean_ctor_get(v_mctx_4066_, 0);
v_levelAssignDepth_4075_ = lean_ctor_get(v_mctx_4066_, 1);
v_lmvarCounter_4076_ = lean_ctor_get(v_mctx_4066_, 2);
v_mvarCounter_4077_ = lean_ctor_get(v_mctx_4066_, 3);
v_lDecls_4078_ = lean_ctor_get(v_mctx_4066_, 4);
v_decls_4079_ = lean_ctor_get(v_mctx_4066_, 5);
v_userNames_4080_ = lean_ctor_get(v_mctx_4066_, 6);
v_lAssignment_4081_ = lean_ctor_get(v_mctx_4066_, 7);
v_eAssignment_4082_ = lean_ctor_get(v_mctx_4066_, 8);
v_dAssignment_4083_ = lean_ctor_get(v_mctx_4066_, 9);
v_synthNormMemo_4084_ = lean_ctor_get(v_mctx_4066_, 10);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_mctx_4066_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4086_ = v_mctx_4066_;
v_isShared_4087_ = v_isSharedCheck_4098_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_synthNormMemo_4084_);
lean_inc(v_dAssignment_4083_);
lean_inc(v_eAssignment_4082_);
lean_inc(v_lAssignment_4081_);
lean_inc(v_userNames_4080_);
lean_inc(v_decls_4079_);
lean_inc(v_lDecls_4078_);
lean_inc(v_mvarCounter_4077_);
lean_inc(v_lmvarCounter_4076_);
lean_inc(v_levelAssignDepth_4075_);
lean_inc(v_depth_4074_);
lean_dec(v_mctx_4066_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4098_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4088_ = lean_box(0);
v___x_4089_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4082_, v_mvarId_4061_, v_val_4062_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 8, v___x_4089_);
v___x_4091_ = v___x_4086_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_depth_4074_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_levelAssignDepth_4075_);
lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_lmvarCounter_4076_);
lean_ctor_set(v_reuseFailAlloc_4097_, 3, v_mvarCounter_4077_);
lean_ctor_set(v_reuseFailAlloc_4097_, 4, v_lDecls_4078_);
lean_ctor_set(v_reuseFailAlloc_4097_, 5, v_decls_4079_);
lean_ctor_set(v_reuseFailAlloc_4097_, 6, v_userNames_4080_);
lean_ctor_set(v_reuseFailAlloc_4097_, 7, v_lAssignment_4081_);
lean_ctor_set(v_reuseFailAlloc_4097_, 8, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4097_, 9, v_dAssignment_4083_);
lean_ctor_set(v_reuseFailAlloc_4097_, 10, v_synthNormMemo_4084_);
v___x_4091_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4093_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v___x_4091_);
v___x_4093_ = v___x_4072_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v_cache_4067_);
lean_ctor_set(v_reuseFailAlloc_4096_, 2, v_zetaDeltaFVarIds_4068_);
lean_ctor_set(v_reuseFailAlloc_4096_, 3, v_postponed_4069_);
lean_ctor_set(v_reuseFailAlloc_4096_, 4, v_diag_4070_);
v___x_4093_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_st_ref_put(v___y_4063_, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4088_);
return v___x_4095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4100_, lean_object* v_val_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4100_, v_val_4101_, v___y_4102_);
lean_dec(v___y_4102_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4107_, uint8_t v_elimTrivial_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_lctx_4114_; lean_object* v___x_4115_; 
v_lctx_4114_ = lean_ctor_get(v___y_4109_, 2);
lean_inc(v_mvar_4107_);
v___x_4115_ = l_Lean_MVarId_getType(v_mvar_4107_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v___x_4115_, 1);
v___x_4117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4118_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4116_, v___x_4117_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v_fst_4120_; lean_object* v_snd_4121_; lean_object* v___x_4122_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v_fst_4120_ = lean_ctor_get(v_a_4119_, 0);
lean_inc(v_fst_4120_);
v_snd_4121_ = lean_ctor_get(v_a_4119_, 1);
lean_inc(v_snd_4121_);
lean_dec(v_a_4119_);
lean_inc_ref(v_lctx_4114_);
v___x_4122_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4114_, v_snd_4121_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; lean_object* v_decls_4125_; lean_object* v___x_4126_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v___x_4124_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4125_ = lean_ctor_get(v_a_4123_, 1);
lean_inc_ref(v_decls_4125_);
lean_dec(v_a_4123_);
v___x_4126_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4108_, v_decls_4125_, v___x_4124_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec_ref(v_decls_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v_fst_4128_; lean_object* v_snd_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v_fst_4128_ = lean_ctor_get(v_a_4127_, 0);
lean_inc(v_fst_4128_);
v_snd_4129_ = lean_ctor_get(v_a_4127_, 1);
lean_inc(v_snd_4129_);
lean_dec(v_a_4127_);
v___x_4130_ = l_Lean_Expr_replaceFVars(v_fst_4120_, v_fst_4128_, v_snd_4129_);
lean_dec(v_snd_4129_);
lean_dec(v_fst_4120_);
v___x_4131_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4130_, v_elimTrivial_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4133_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
lean_inc(v_mvar_4107_);
v___x_4133_ = l_Lean_MVarId_getTag(v_mvar_4107_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4135_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v___x_4133_, 1);
v___x_4135_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4132_, v_a_4134_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; size_t v_sz_4139_; size_t v___x_4140_; lean_object* v___x_4141_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc_n(v_a_4136_, 2);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4107_, v_a_4136_, v___y_4110_);
lean_dec_ref(v___x_4137_);
v___x_4138_ = l_Lean_Expr_mvarId_x21(v_a_4136_);
lean_dec(v_a_4136_);
v_sz_4139_ = lean_array_size(v_fst_4128_);
v___x_4140_ = ((size_t)0ULL);
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4128_, v_sz_4139_, v___x_4140_, v___x_4138_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec_ref(v___y_4109_);
lean_dec(v_fst_4128_);
return v___x_4141_;
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_fst_4128_);
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4142_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4135_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4135_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v_a_4132_);
lean_dec(v_fst_4128_);
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4150_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4133_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4133_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v_fst_4128_);
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4158_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4131_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4131_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_fst_4120_);
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4166_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4126_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4126_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_dec(v_fst_4120_);
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4174_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4122_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4122_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4182_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4118_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4118_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec_ref(v___y_4109_);
lean_dec(v_mvar_4107_);
v_a_4190_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4115_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4115_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4198_, lean_object* v_elimTrivial_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_elimTrivial_boxed_4205_; lean_object* v_res_4206_; 
v_elimTrivial_boxed_4205_ = lean_unbox(v_elimTrivial_4199_);
v_res_4206_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4198_, v_elimTrivial_boxed_4205_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4207_, uint8_t v_elimTrivial_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; 
v___x_4214_ = lean_box(v_elimTrivial_4208_);
lean_inc(v_mvar_4207_);
v___f_4215_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4215_, 0, v_mvar_4207_);
lean_closure_set(v___f_4215_, 1, v___x_4214_);
v___x_4216_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4207_, v___f_4215_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4217_, lean_object* v_elimTrivial_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
uint8_t v_elimTrivial_boxed_4224_; lean_object* v_res_4225_; 
v_elimTrivial_boxed_4224_ = lean_unbox(v_elimTrivial_4218_);
v_res_4225_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4217_, v_elimTrivial_boxed_4224_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4226_, lean_object* v_val_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4226_, v_val_4227_, v___y_4229_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4234_, lean_object* v_val_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4234_, v_val_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4242_, lean_object* v_x_4243_, lean_object* v_x_4244_, lean_object* v_x_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4243_, v_x_4244_, v_x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4247_, lean_object* v_as_4248_, size_t v_sz_4249_, size_t v_i_4250_, lean_object* v_b_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4247_, v_as_4248_, v_sz_4249_, v_i_4250_, v_b_4251_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4258_, lean_object* v_as_4259_, lean_object* v_sz_4260_, lean_object* v_i_4261_, lean_object* v_b_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
uint8_t v_elimTrivial_boxed_4268_; size_t v_sz_boxed_4269_; size_t v_i_boxed_4270_; lean_object* v_res_4271_; 
v_elimTrivial_boxed_4268_ = lean_unbox(v_elimTrivial_4258_);
v_sz_boxed_4269_ = lean_unbox_usize(v_sz_4260_);
lean_dec(v_sz_4260_);
v_i_boxed_4270_ = lean_unbox_usize(v_i_4261_);
lean_dec(v_i_4261_);
v_res_4271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4268_, v_as_4259_, v_sz_boxed_4269_, v_i_boxed_4270_, v_b_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v_as_4259_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4272_, lean_object* v_x_4273_, size_t v_x_4274_, size_t v_x_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4273_, v_x_4274_, v_x_4275_, v_x_4276_, v_x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_, lean_object* v_x_4284_){
_start:
{
size_t v_x_8268__boxed_4285_; size_t v_x_8269__boxed_4286_; lean_object* v_res_4287_; 
v_x_8268__boxed_4285_ = lean_unbox_usize(v_x_4281_);
lean_dec(v_x_4281_);
v_x_8269__boxed_4286_ = lean_unbox_usize(v_x_4282_);
lean_dec(v_x_4282_);
v_res_4287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4279_, v_x_4280_, v_x_8268__boxed_4285_, v_x_8269__boxed_4286_, v_x_4283_, v_x_4284_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4288_, lean_object* v_as_4289_, size_t v_sz_4290_, size_t v_i_4291_, lean_object* v_b_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4288_, v_as_4289_, v_sz_4290_, v_i_4291_, v_b_4292_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4299_, lean_object* v_as_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_b_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
uint8_t v_elimTrivial_boxed_4309_; size_t v_sz_boxed_4310_; size_t v_i_boxed_4311_; lean_object* v_res_4312_; 
v_elimTrivial_boxed_4309_ = lean_unbox(v_elimTrivial_4299_);
v_sz_boxed_4310_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4311_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4309_, v_as_4300_, v_sz_boxed_4310_, v_i_boxed_4311_, v_b_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_as_4300_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4313_, lean_object* v_n_4314_, lean_object* v_k_4315_, lean_object* v_v_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4314_, v_k_4315_, v_v_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4318_, size_t v_depth_4319_, lean_object* v_keys_4320_, lean_object* v_vals_4321_, lean_object* v_heq_4322_, lean_object* v_i_4323_, lean_object* v_entries_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4319_, v_keys_4320_, v_vals_4321_, v_i_4323_, v_entries_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4326_, lean_object* v_depth_4327_, lean_object* v_keys_4328_, lean_object* v_vals_4329_, lean_object* v_heq_4330_, lean_object* v_i_4331_, lean_object* v_entries_4332_){
_start:
{
size_t v_depth_boxed_4333_; lean_object* v_res_4334_; 
v_depth_boxed_4333_ = lean_unbox_usize(v_depth_4327_);
lean_dec(v_depth_4327_);
v_res_4334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4326_, v_depth_boxed_4333_, v_keys_4328_, v_vals_4329_, v_heq_4330_, v_i_4331_, v_entries_4332_);
lean_dec_ref(v_vals_4329_);
lean_dec_ref(v_keys_4328_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4335_, lean_object* v_x_4336_, lean_object* v_x_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4336_, v_x_4337_, v_x_4338_, v_x_4339_);
return v___x_4340_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedUses_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 = _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
#ifdef __cplusplus
}
#endif
