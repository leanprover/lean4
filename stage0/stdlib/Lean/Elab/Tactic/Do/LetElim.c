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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isOfNatNatLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfScientificLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isCharLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; 
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
v___x_1175_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1169_);
v___x_1176_ = l_Lean_KVMap_setNat(v___x_1173_, v___x_1174_, v___x_1175_);
v___x_1177_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1176_, v_fst_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1172_);
lean_ctor_set(v___x_1166_, 0, v___y_1170_);
v___x_1179_ = v___x_1166_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___y_1170_);
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
v___y_1169_ = v___x_1195_;
v___y_1170_ = v_fst_1186_;
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
v___y_1169_ = v___x_1196_;
v___y_1170_ = v_fst_1186_;
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
lean_object* v___y_1872_; lean_object* v_toCold_1881_; lean_object* v_currRecDepth_1882_; lean_object* v_ref_1883_; uint16_t v_optionFlags_1884_; uint8_t v_suppressElabErrors_1885_; uint8_t v_checkDeprecated_1886_; uint8_t v_isRecordingDeps_1887_; lean_object* v_maxRecDepth_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_toCold_1881_ = lean_ctor_get(v___y_1868_, 0);
v_currRecDepth_1882_ = lean_ctor_get(v___y_1868_, 1);
v_ref_1883_ = lean_ctor_get(v___y_1868_, 2);
v_optionFlags_1884_ = lean_ctor_get_uint16(v___y_1868_, sizeof(void*)*3);
v_suppressElabErrors_1885_ = lean_ctor_get_uint8(v___y_1868_, sizeof(void*)*3 + 2);
v_checkDeprecated_1886_ = lean_ctor_get_uint8(v___y_1868_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1887_ = lean_ctor_get_uint8(v___y_1868_, sizeof(void*)*3 + 4);
v_maxRecDepth_1893_ = lean_ctor_get(v_toCold_1881_, 3);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_nat_dec_eq(v_maxRecDepth_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_eq(v_currRecDepth_1882_, v_maxRecDepth_1893_);
if (v___x_1896_ == 0)
{
goto v___jp_1888_;
}
else
{
lean_object* v___x_1897_; 
lean_dec_ref(v_x_1863_);
lean_inc(v_ref_1883_);
v___x_1897_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1883_);
v___y_1872_ = v___x_1897_;
goto v___jp_1871_;
}
}
else
{
goto v___jp_1888_;
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
v___jp_1888_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_nat_add(v_currRecDepth_1882_, v___x_1889_);
lean_inc(v_ref_1883_);
lean_inc_ref(v_toCold_1881_);
v___x_1891_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1891_, 0, v_toCold_1881_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
lean_ctor_set(v___x_1891_, 2, v_ref_1883_);
lean_ctor_set_uint16(v___x_1891_, sizeof(void*)*3, v_optionFlags_1884_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 2, v_suppressElabErrors_1885_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 3, v_checkDeprecated_1886_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 4, v_isRecordingDeps_1887_);
lean_inc(v___y_1869_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc(v___y_1864_);
v___x_1892_ = lean_apply_7(v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___x_1891_, v___y_1869_, lean_box(0));
v___y_1872_ = v___x_1892_;
goto v___jp_1871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_box(0);
return v___x_1909_;
}
else
{
lean_object* v_key_1910_; lean_object* v_value_1911_; lean_object* v_tail_1912_; uint8_t v___x_1913_; 
v_key_1910_ = lean_ctor_get(v_x_1908_, 0);
v_value_1911_ = lean_ctor_get(v_x_1908_, 1);
v_tail_1912_ = lean_ctor_get(v_x_1908_, 2);
v___x_1913_ = l_Lean_ExprStructEq_beq(v_key_1910_, v_a_1907_);
if (v___x_1913_ == 0)
{
v_x_1908_ = v_tail_1912_;
goto _start;
}
else
{
lean_object* v___x_1915_; 
lean_inc(v_value_1911_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_value_1911_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1916_, v_x_1917_);
lean_dec(v_x_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_buckets_1921_; lean_object* v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; uint64_t v___x_1925_; uint64_t v_fold_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_buckets_1921_ = lean_ctor_get(v_m_1919_, 1);
v___x_1922_ = lean_array_get_size(v_buckets_1921_);
v___x_1923_ = l_Lean_ExprStructEq_hash(v_a_1920_);
v___x_1924_ = 32ULL;
v___x_1925_ = lean_uint64_shift_right(v___x_1923_, v___x_1924_);
v_fold_1926_ = lean_uint64_xor(v___x_1923_, v___x_1925_);
v___x_1927_ = 16ULL;
v___x_1928_ = lean_uint64_shift_right(v_fold_1926_, v___x_1927_);
v___x_1929_ = lean_uint64_xor(v_fold_1926_, v___x_1928_);
v___x_1930_ = lean_uint64_to_usize(v___x_1929_);
v___x_1931_ = lean_usize_of_nat(v___x_1922_);
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_sub(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_usize_land(v___x_1930_, v___x_1933_);
v___x_1935_ = lean_array_uget_borrowed(v_buckets_1921_, v___x_1934_);
v___x_1936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1920_, v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1937_, v_a_1938_);
lean_dec_ref(v_a_1938_);
lean_dec_ref(v_m_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
lean_inc(v___y_1947_);
lean_inc_ref(v___y_1946_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1942_);
lean_inc(v___y_1941_);
v___x_1949_ = lean_apply_8(v_k_1940_, v_b_1943_, v___y_1941_, v___y_1942_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, lean_box(0));
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1950_, v___y_1951_, v___y_1952_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1952_);
lean_dec(v___y_1951_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1960_, lean_object* v_type_1961_, lean_object* v_val_1962_, lean_object* v_k_1963_, uint8_t v_nondep_1964_, uint8_t v_kind_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___f_1973_; lean_object* v___x_1974_; 
lean_inc(v___y_1967_);
lean_inc(v___y_1966_);
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1973_, 0, v_k_1963_);
lean_closure_set(v___f_1973_, 1, v___y_1966_);
lean_closure_set(v___f_1973_, 2, v___y_1967_);
v___x_1974_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1960_, v_type_1961_, v_val_1962_, v___f_1973_, v_nondep_1964_, v_kind_1965_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1974_) == 0)
{
return v___x_1974_;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1983_, lean_object* v_type_1984_, lean_object* v_val_1985_, lean_object* v_k_1986_, lean_object* v_nondep_1987_, lean_object* v_kind_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v_nondep_boxed_1996_; uint8_t v_kind_boxed_1997_; lean_object* v_res_1998_; 
v_nondep_boxed_1996_ = lean_unbox(v_nondep_1987_);
v_kind_boxed_1997_ = lean_unbox(v_kind_1988_);
v_res_1998_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1983_, v_type_1984_, v_val_1985_, v_k_1986_, v_nondep_boxed_1996_, v_kind_boxed_1997_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_1999_, uint8_t v_bi_2000_, lean_object* v_type_2001_, lean_object* v_k_2002_, uint8_t v_kind_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___f_2011_; lean_object* v___x_2012_; 
lean_inc(v___y_2005_);
lean_inc(v___y_2004_);
v___f_2011_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2011_, 0, v_k_2002_);
lean_closure_set(v___f_2011_, 1, v___y_2004_);
lean_closure_set(v___f_2011_, 2, v___y_2005_);
v___x_2012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1999_, v_bi_2000_, v_type_2001_, v___f_2011_, v_kind_2003_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2012_) == 0)
{
return v___x_2012_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2021_, lean_object* v_bi_2022_, lean_object* v_type_2023_, lean_object* v_k_2024_, lean_object* v_kind_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v_bi_boxed_2033_; uint8_t v_kind_boxed_2034_; lean_object* v_res_2035_; 
v_bi_boxed_2033_ = lean_unbox(v_bi_2022_);
v_kind_boxed_2034_ = lean_unbox(v_kind_2025_);
v_res_2035_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2021_, v_bi_boxed_2033_, v_type_2023_, v_k_2024_, v_kind_boxed_2034_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2036_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_apply_1(v_x_2053_, lean_box(0));
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_x_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2062_, v_x_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
return v_x_2071_;
}
else
{
lean_object* v_key_2073_; lean_object* v_value_2074_; lean_object* v_tail_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2098_; 
v_key_2073_ = lean_ctor_get(v_x_2072_, 0);
v_value_2074_ = lean_ctor_get(v_x_2072_, 1);
v_tail_2075_ = lean_ctor_get(v_x_2072_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2077_ = v_x_2072_;
v_isShared_2078_ = v_isSharedCheck_2098_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_tail_2075_);
lean_inc(v_value_2074_);
lean_inc(v_key_2073_);
lean_dec(v_x_2072_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2098_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; uint64_t v_fold_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2079_ = lean_array_get_size(v_x_2071_);
v___x_2080_ = l_Lean_ExprStructEq_hash(v_key_2073_);
v___x_2081_ = 32ULL;
v___x_2082_ = lean_uint64_shift_right(v___x_2080_, v___x_2081_);
v_fold_2083_ = lean_uint64_xor(v___x_2080_, v___x_2082_);
v___x_2084_ = 16ULL;
v___x_2085_ = lean_uint64_shift_right(v_fold_2083_, v___x_2084_);
v___x_2086_ = lean_uint64_xor(v_fold_2083_, v___x_2085_);
v___x_2087_ = lean_uint64_to_usize(v___x_2086_);
v___x_2088_ = lean_usize_of_nat(v___x_2079_);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_sub(v___x_2088_, v___x_2089_);
v___x_2091_ = lean_usize_land(v___x_2087_, v___x_2090_);
v___x_2092_ = lean_array_uget_borrowed(v_x_2071_, v___x_2091_);
lean_inc(v___x_2092_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 2, v___x_2092_);
v___x_2094_ = v___x_2077_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_key_2073_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_value_2074_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_array_uset(v_x_2071_, v___x_2091_, v___x_2094_);
v_x_2071_ = v___x_2095_;
v_x_2072_ = v_tail_2075_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2099_, lean_object* v_source_2100_, lean_object* v_target_2101_){
_start:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_array_get_size(v_source_2100_);
v___x_2103_ = lean_nat_dec_lt(v_i_2099_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v_source_2100_);
lean_dec(v_i_2099_);
return v_target_2101_;
}
else
{
lean_object* v_es_2104_; lean_object* v___x_2105_; lean_object* v_source_2106_; lean_object* v_target_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_es_2104_ = lean_array_fget(v_source_2100_, v_i_2099_);
v___x_2105_ = lean_box(0);
v_source_2106_ = lean_array_fset(v_source_2100_, v_i_2099_, v___x_2105_);
v_target_2107_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2101_, v_es_2104_);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_add(v_i_2099_, v___x_2108_);
lean_dec(v_i_2099_);
v_i_2099_ = v___x_2109_;
v_source_2100_ = v_source_2106_;
v_target_2101_ = v_target_2107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2111_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_nbuckets_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2112_ = lean_array_get_size(v_data_2111_);
v___x_2113_ = lean_unsigned_to_nat(2u);
v_nbuckets_2114_ = lean_nat_mul(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_mk_array(v_nbuckets_2114_, v___x_2116_);
v___x_2118_ = lean_array_propagate_mark(v_data_2111_, v___x_2117_);
v___x_2119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2115_, v_data_2111_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2120_, lean_object* v_b_2121_, lean_object* v_x_2122_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_dec(v_b_2121_);
lean_dec_ref(v_a_2120_);
return v_x_2122_;
}
else
{
lean_object* v_key_2123_; lean_object* v_value_2124_; lean_object* v_tail_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2137_; 
v_key_2123_ = lean_ctor_get(v_x_2122_, 0);
v_value_2124_ = lean_ctor_get(v_x_2122_, 1);
v_tail_2125_ = lean_ctor_get(v_x_2122_, 2);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2127_ = v_x_2122_;
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_tail_2125_);
lean_inc(v_value_2124_);
lean_inc(v_key_2123_);
lean_dec(v_x_2122_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint8_t v___x_2129_; 
v___x_2129_ = l_Lean_ExprStructEq_beq(v_key_2123_, v_a_2120_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2120_, v_b_2121_, v_tail_2125_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 2, v___x_2130_);
v___x_2132_ = v___x_2127_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_key_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_value_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_value_2124_);
lean_dec(v_key_2123_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_b_2121_);
lean_ctor_set(v___x_2127_, 0, v_a_2120_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_b_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_tail_2125_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = 0;
return v___x_2140_;
}
else
{
lean_object* v_key_2141_; lean_object* v_tail_2142_; uint8_t v___x_2143_; 
v_key_2141_ = lean_ctor_get(v_x_2139_, 0);
v_tail_2142_ = lean_ctor_get(v_x_2139_, 2);
v___x_2143_ = l_Lean_ExprStructEq_beq(v_key_2141_, v_a_2138_);
if (v___x_2143_ == 0)
{
v_x_2139_ = v_tail_2142_;
goto _start;
}
else
{
return v___x_2143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2145_, lean_object* v_x_2146_){
_start:
{
uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_res_2147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2145_, v_x_2146_);
lean_dec(v_x_2146_);
lean_dec_ref(v_a_2145_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2149_, lean_object* v_a_2150_, lean_object* v_b_2151_){
_start:
{
lean_object* v_size_2152_; lean_object* v_buckets_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2196_; 
v_size_2152_ = lean_ctor_get(v_m_2149_, 0);
v_buckets_2153_ = lean_ctor_get(v_m_2149_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_m_2149_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2155_ = v_m_2149_;
v_isShared_2156_ = v_isSharedCheck_2196_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_buckets_2153_);
lean_inc(v_size_2152_);
lean_dec(v_m_2149_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2196_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; uint64_t v___x_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; uint64_t v_fold_2161_; uint64_t v___x_2162_; uint64_t v___x_2163_; uint64_t v___x_2164_; size_t v___x_2165_; size_t v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; lean_object* v_bkt_2170_; uint8_t v___x_2171_; 
v___x_2157_ = lean_array_get_size(v_buckets_2153_);
v___x_2158_ = l_Lean_ExprStructEq_hash(v_a_2150_);
v___x_2159_ = 32ULL;
v___x_2160_ = lean_uint64_shift_right(v___x_2158_, v___x_2159_);
v_fold_2161_ = lean_uint64_xor(v___x_2158_, v___x_2160_);
v___x_2162_ = 16ULL;
v___x_2163_ = lean_uint64_shift_right(v_fold_2161_, v___x_2162_);
v___x_2164_ = lean_uint64_xor(v_fold_2161_, v___x_2163_);
v___x_2165_ = lean_uint64_to_usize(v___x_2164_);
v___x_2166_ = lean_usize_of_nat(v___x_2157_);
v___x_2167_ = ((size_t)1ULL);
v___x_2168_ = lean_usize_sub(v___x_2166_, v___x_2167_);
v___x_2169_ = lean_usize_land(v___x_2165_, v___x_2168_);
v_bkt_2170_ = lean_array_uget_borrowed(v_buckets_2153_, v___x_2169_);
v___x_2171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2150_, v_bkt_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v_size_x27_2173_; lean_object* v___x_2174_; lean_object* v_buckets_x27_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v_size_x27_2173_ = lean_nat_add(v_size_2152_, v___x_2172_);
lean_dec(v_size_2152_);
lean_inc(v_bkt_2170_);
v___x_2174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2174_, 0, v_a_2150_);
lean_ctor_set(v___x_2174_, 1, v_b_2151_);
lean_ctor_set(v___x_2174_, 2, v_bkt_2170_);
v_buckets_x27_2175_ = lean_array_uset(v_buckets_2153_, v___x_2169_, v___x_2174_);
v___x_2176_ = lean_unsigned_to_nat(4u);
v___x_2177_ = lean_nat_mul(v_size_x27_2173_, v___x_2176_);
v___x_2178_ = lean_unsigned_to_nat(3u);
v___x_2179_ = lean_nat_div(v___x_2177_, v___x_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_array_get_size(v_buckets_x27_2175_);
v___x_2181_ = lean_nat_dec_le(v___x_2179_, v___x_2180_);
lean_dec(v___x_2179_);
if (v___x_2181_ == 0)
{
lean_object* v_val_2182_; lean_object* v___x_2184_; 
v_val_2182_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2175_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_val_2182_);
lean_ctor_set(v___x_2155_, 0, v_size_x27_2173_);
v___x_2184_ = v___x_2155_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_size_x27_2173_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_val_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
lean_object* v___x_2187_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_buckets_x27_2175_);
lean_ctor_set(v___x_2155_, 0, v_size_x27_2173_);
v___x_2187_ = v___x_2155_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_size_x27_2173_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_buckets_x27_2175_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v_buckets_x27_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
lean_inc(v_bkt_2170_);
v___x_2189_ = lean_box(0);
v_buckets_x27_2190_ = lean_array_uset(v_buckets_2153_, v___x_2169_, v___x_2189_);
v___x_2191_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2150_, v_b_2151_, v_bkt_2170_);
v___x_2192_ = lean_array_uset(v_buckets_x27_2190_, v___x_2169_, v___x_2191_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2192_);
v___x_2194_ = v___x_2155_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_size_2152_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2197_, lean_object* v_e_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = lean_st_ref_take(v_a_2197_);
v___x_2202_ = lean_box(0);
v___x_2203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2201_, v_e_2198_, v_a_2199_);
v___x_2204_ = lean_st_ref_put(v_a_2197_, v___x_2203_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2205_, lean_object* v_e_2206_, lean_object* v_a_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2205_, v_e_2206_, v_a_2207_);
lean_dec(v_a_2205_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2210_, lean_object* v_pre_2211_, lean_object* v_post_2212_, lean_object* v_usedLetOnly_2213_, lean_object* v_skipConstInApp_2214_, lean_object* v_skipInstances_2215_, lean_object* v_body_2216_, lean_object* v_x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
uint8_t v_usedLetOnly_boxed_2225_; uint8_t v_skipConstInApp_boxed_2226_; uint8_t v_skipInstances_boxed_2227_; lean_object* v_res_2228_; 
v_usedLetOnly_boxed_2225_ = lean_unbox(v_usedLetOnly_2213_);
v_skipConstInApp_boxed_2226_ = lean_unbox(v_skipConstInApp_2214_);
v_skipInstances_boxed_2227_ = lean_unbox(v_skipInstances_2215_);
v_res_2228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2210_, v_pre_2211_, v_post_2212_, v_usedLetOnly_boxed_2225_, v_skipConstInApp_boxed_2226_, v_skipInstances_boxed_2227_, v_body_2216_, v_x_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec(v___y_2218_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2232_, lean_object* v_pre_2233_, lean_object* v_post_2234_, uint8_t v_usedLetOnly_2235_, uint8_t v_skipConstInApp_2236_, uint8_t v_skipInstances_2237_, lean_object* v_body_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_array_push(v_fvars_2232_, v_x_2239_);
v___x_2248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2233_, v_post_2234_, v_usedLetOnly_2235_, v_skipConstInApp_2236_, v_skipInstances_2237_, v___x_2247_, v_body_2238_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2249_, lean_object* v_pre_2250_, lean_object* v_post_2251_, lean_object* v_usedLetOnly_2252_, lean_object* v_skipConstInApp_2253_, lean_object* v_skipInstances_2254_, lean_object* v_body_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_usedLetOnly_boxed_2264_; uint8_t v_skipConstInApp_boxed_2265_; uint8_t v_skipInstances_boxed_2266_; lean_object* v_res_2267_; 
v_usedLetOnly_boxed_2264_ = lean_unbox(v_usedLetOnly_2252_);
v_skipConstInApp_boxed_2265_ = lean_unbox(v_skipConstInApp_2253_);
v_skipInstances_boxed_2266_ = lean_unbox(v_skipInstances_2254_);
v_res_2267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2249_, v_pre_2250_, v_post_2251_, v_usedLetOnly_boxed_2264_, v_skipConstInApp_boxed_2265_, v_skipInstances_boxed_2266_, v_body_2255_, v_x_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2257_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2268_, lean_object* v_post_2269_, uint8_t v_usedLetOnly_2270_, uint8_t v_skipConstInApp_2271_, uint8_t v_skipInstances_2272_, lean_object* v_e_2273_, lean_object* v_a_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
lean_inc_ref(v_post_2269_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v_e_2273_);
v___x_2281_ = lean_apply_7(v_post_2269_, v_e_2273_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, lean_box(0));
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2300_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2300_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2300_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
switch(lean_obj_tag(v_a_2282_))
{
case 0:
{
lean_object* v_e_2286_; lean_object* v___x_2288_; 
lean_dec_ref(v_e_2273_);
lean_dec_ref(v_post_2269_);
lean_dec_ref(v_pre_2268_);
v_e_2286_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_e_2286_);
lean_dec_ref_known(v_a_2282_, 1);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v_e_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_e_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
case 1:
{
lean_object* v_e_2290_; lean_object* v___x_2291_; 
lean_del_object(v___x_2284_);
lean_dec_ref(v_e_2273_);
v_e_2290_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_e_2290_);
lean_dec_ref_known(v_a_2282_, 1);
v___x_2291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2268_, v_post_2269_, v_usedLetOnly_2270_, v_skipConstInApp_2271_, v_skipInstances_2272_, v_e_2290_, v_a_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2291_;
}
default: 
{
lean_object* v_e_x3f_2292_; 
lean_dec_ref(v_post_2269_);
lean_dec_ref(v_pre_2268_);
v_e_x3f_2292_ = lean_ctor_get(v_a_2282_, 0);
lean_inc(v_e_x3f_2292_);
lean_dec_ref_known(v_a_2282_, 1);
if (lean_obj_tag(v_e_x3f_2292_) == 0)
{
lean_object* v___x_2294_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v_e_2273_);
v___x_2294_ = v___x_2284_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_e_2273_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
else
{
lean_object* v_val_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_e_2273_);
v_val_2296_ = lean_ctor_get(v_e_x3f_2292_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v_e_x3f_2292_, 1);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v_val_2296_);
v___x_2298_ = v___x_2284_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_val_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_e_2273_);
lean_dec_ref(v_post_2269_);
lean_dec_ref(v_pre_2268_);
v_a_2301_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2281_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2281_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2309_, lean_object* v_post_2310_, uint8_t v_usedLetOnly_2311_, uint8_t v_skipConstInApp_2312_, uint8_t v_skipInstances_2313_, lean_object* v_fvars_2314_, lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
if (lean_obj_tag(v_e_2315_) == 6)
{
lean_object* v_binderName_2323_; lean_object* v_binderType_2324_; lean_object* v_body_2325_; uint8_t v_binderInfo_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_binderName_2323_ = lean_ctor_get(v_e_2315_, 0);
lean_inc(v_binderName_2323_);
v_binderType_2324_ = lean_ctor_get(v_e_2315_, 1);
lean_inc_ref(v_binderType_2324_);
v_body_2325_ = lean_ctor_get(v_e_2315_, 2);
lean_inc_ref(v_body_2325_);
v_binderInfo_2326_ = lean_ctor_get_uint8(v_e_2315_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2315_, 3);
v___x_2327_ = lean_box(v_usedLetOnly_2311_);
v___x_2328_ = lean_box(v_skipConstInApp_2312_);
v___x_2329_ = lean_box(v_skipInstances_2313_);
lean_inc_ref(v_post_2310_);
lean_inc_ref(v_pre_2309_);
lean_inc_ref(v_fvars_2314_);
v___f_2330_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2330_, 0, v_fvars_2314_);
lean_closure_set(v___f_2330_, 1, v_pre_2309_);
lean_closure_set(v___f_2330_, 2, v_post_2310_);
lean_closure_set(v___f_2330_, 3, v___x_2327_);
lean_closure_set(v___f_2330_, 4, v___x_2328_);
lean_closure_set(v___f_2330_, 5, v___x_2329_);
lean_closure_set(v___f_2330_, 6, v_body_2325_);
v___x_2331_ = lean_expr_instantiate_rev(v_binderType_2324_, v_fvars_2314_);
lean_dec_ref(v_fvars_2314_);
lean_dec_ref(v_binderType_2324_);
v___x_2332_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2309_, v_post_2310_, v_usedLetOnly_2311_, v_skipConstInApp_2312_, v_skipInstances_2313_, v___x_2331_, v_a_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = 0;
v___x_2335_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2323_, v_binderInfo_2326_, v_a_2333_, v___f_2330_, v___x_2334_, v_a_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2335_;
}
else
{
lean_dec_ref(v___f_2330_);
lean_dec(v_binderName_2323_);
return v___x_2332_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_expr_instantiate_rev(v_e_2315_, v_fvars_2314_);
lean_dec_ref(v_e_2315_);
lean_inc_ref(v_post_2310_);
lean_inc_ref(v_pre_2309_);
v___x_2337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2309_, v_post_2310_, v_usedLetOnly_2311_, v_skipConstInApp_2312_, v_skipInstances_2313_, v___x_2336_, v_a_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = 0;
v___x_2340_ = 1;
v___x_2341_ = 1;
v___x_2342_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2314_, v_a_2338_, v___x_2339_, v_usedLetOnly_2311_, v___x_2339_, v___x_2340_, v___x_2341_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec_ref(v_fvars_2314_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2309_, v_post_2310_, v_usedLetOnly_2311_, v_skipConstInApp_2312_, v_skipInstances_2313_, v_a_2343_, v_a_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2344_;
}
else
{
lean_dec_ref(v_post_2310_);
lean_dec_ref(v_pre_2309_);
return v___x_2342_;
}
}
else
{
lean_dec_ref(v_fvars_2314_);
lean_dec_ref(v_post_2310_);
lean_dec_ref(v_pre_2309_);
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2345_, lean_object* v_pre_2346_, lean_object* v_post_2347_, uint8_t v_usedLetOnly_2348_, uint8_t v_skipConstInApp_2349_, uint8_t v_skipInstances_2350_, lean_object* v_body_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_array_push(v_fvars_2345_, v_x_2352_);
v___x_2361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2346_, v_post_2347_, v_usedLetOnly_2348_, v_skipConstInApp_2349_, v_skipInstances_2350_, v___x_2360_, v_body_2351_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2362_, lean_object* v_pre_2363_, lean_object* v_post_2364_, lean_object* v_usedLetOnly_2365_, lean_object* v_skipConstInApp_2366_, lean_object* v_skipInstances_2367_, lean_object* v_body_2368_, lean_object* v_x_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
uint8_t v_usedLetOnly_boxed_2377_; uint8_t v_skipConstInApp_boxed_2378_; uint8_t v_skipInstances_boxed_2379_; lean_object* v_res_2380_; 
v_usedLetOnly_boxed_2377_ = lean_unbox(v_usedLetOnly_2365_);
v_skipConstInApp_boxed_2378_ = lean_unbox(v_skipConstInApp_2366_);
v_skipInstances_boxed_2379_ = lean_unbox(v_skipInstances_2367_);
v_res_2380_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2362_, v_pre_2363_, v_post_2364_, v_usedLetOnly_boxed_2377_, v_skipConstInApp_boxed_2378_, v_skipInstances_boxed_2379_, v_body_2368_, v_x_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2381_, lean_object* v_post_2382_, uint8_t v_usedLetOnly_2383_, uint8_t v_skipConstInApp_2384_, uint8_t v_skipInstances_2385_, lean_object* v_fvars_2386_, lean_object* v_e_2387_, lean_object* v_a_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
if (lean_obj_tag(v_e_2387_) == 8)
{
lean_object* v_declName_2395_; lean_object* v_type_2396_; lean_object* v_value_2397_; lean_object* v_body_2398_; uint8_t v_nondep_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_declName_2395_ = lean_ctor_get(v_e_2387_, 0);
lean_inc(v_declName_2395_);
v_type_2396_ = lean_ctor_get(v_e_2387_, 1);
lean_inc_ref(v_type_2396_);
v_value_2397_ = lean_ctor_get(v_e_2387_, 2);
lean_inc_ref(v_value_2397_);
v_body_2398_ = lean_ctor_get(v_e_2387_, 3);
lean_inc_ref(v_body_2398_);
v_nondep_2399_ = lean_ctor_get_uint8(v_e_2387_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2387_, 4);
v___x_2400_ = lean_box(v_usedLetOnly_2383_);
v___x_2401_ = lean_box(v_skipConstInApp_2384_);
v___x_2402_ = lean_box(v_skipInstances_2385_);
lean_inc_ref_n(v_post_2382_, 2);
lean_inc_ref_n(v_pre_2381_, 2);
lean_inc_ref(v_fvars_2386_);
v___f_2403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2403_, 0, v_fvars_2386_);
lean_closure_set(v___f_2403_, 1, v_pre_2381_);
lean_closure_set(v___f_2403_, 2, v_post_2382_);
lean_closure_set(v___f_2403_, 3, v___x_2400_);
lean_closure_set(v___f_2403_, 4, v___x_2401_);
lean_closure_set(v___f_2403_, 5, v___x_2402_);
lean_closure_set(v___f_2403_, 6, v_body_2398_);
v___x_2404_ = lean_expr_instantiate_rev(v_type_2396_, v_fvars_2386_);
lean_dec_ref(v_type_2396_);
v___x_2405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v___x_2404_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = lean_expr_instantiate_rev(v_value_2397_, v_fvars_2386_);
lean_dec_ref(v_fvars_2386_);
lean_dec_ref(v_value_2397_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v___x_2407_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = 0;
v___x_2411_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2395_, v_a_2406_, v_a_2409_, v___f_2403_, v_nondep_2399_, v___x_2410_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2411_;
}
else
{
lean_dec(v_a_2406_);
lean_dec_ref(v___f_2403_);
lean_dec(v_declName_2395_);
return v___x_2408_;
}
}
else
{
lean_dec_ref(v___f_2403_);
lean_dec_ref(v_value_2397_);
lean_dec(v_declName_2395_);
lean_dec_ref(v_fvars_2386_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2381_);
return v___x_2405_;
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_expr_instantiate_rev(v_e_2387_, v_fvars_2386_);
lean_dec_ref(v_e_2387_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2381_);
v___x_2413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v___x_2412_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; uint8_t v___x_2415_; uint8_t v___x_2416_; lean_object* v___x_2417_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v___x_2415_ = 0;
v___x_2416_ = 1;
v___x_2417_ = l_Lean_Meta_mkLetFVars(v_fvars_2386_, v_a_2414_, v_usedLetOnly_2383_, v___x_2415_, v___x_2416_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec_ref(v_fvars_2386_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v_a_2418_, v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2419_;
}
else
{
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2381_);
return v___x_2417_;
}
}
else
{
lean_dec_ref(v_fvars_2386_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2381_);
return v___x_2413_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v_dummy_2421_; 
v___x_2420_ = lean_box(0);
v_dummy_2421_ = l_Lean_Expr_sort___override(v___x_2420_);
return v_dummy_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2422_, lean_object* v_post_2423_, uint8_t v_usedLetOnly_2424_, uint8_t v_skipConstInApp_2425_, uint8_t v_skipInstances_2426_, size_t v_sz_2427_, size_t v_i_2428_, lean_object* v_bs_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_dec_ref(v_post_2423_);
lean_dec_ref(v_pre_2422_);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_bs_2429_);
return v___x_2438_;
}
else
{
lean_object* v_v_2439_; lean_object* v___x_2440_; lean_object* v_bs_x27_2441_; lean_object* v___x_2442_; 
v_v_2439_ = lean_array_uget(v_bs_2429_, v_i_2428_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v_bs_x27_2441_ = lean_array_uset(v_bs_2429_, v_i_2428_, v___x_2440_);
lean_inc_ref(v_post_2423_);
lean_inc_ref(v_pre_2422_);
v___x_2442_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2422_, v_post_2423_, v_usedLetOnly_2424_, v_skipConstInApp_2425_, v_skipInstances_2426_, v_v_2439_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; size_t v___x_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2444_ = ((size_t)1ULL);
v___x_2445_ = lean_usize_add(v_i_2428_, v___x_2444_);
v___x_2446_ = lean_array_uset(v_bs_x27_2441_, v_i_2428_, v_a_2443_);
v_i_2428_ = v___x_2445_;
v_bs_2429_ = v___x_2446_;
goto _start;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref(v_bs_x27_2441_);
lean_dec_ref(v_post_2423_);
lean_dec_ref(v_pre_2422_);
v_a_2448_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2442_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2456_, lean_object* v_post_2457_, uint8_t v_usedLetOnly_2458_, uint8_t v_skipConstInApp_2459_, uint8_t v_skipInstances_2460_, lean_object* v___x_2461_, lean_object* v___y_2462_, lean_object* v_b_2463_, lean_object* v_a_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2456_, v_post_2457_, v_usedLetOnly_2458_, v_skipConstInApp_2459_, v_skipInstances_2460_, v___x_2461_, v___y_2462_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2481_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2476_ = lean_array_fset(v_b_2463_, v_a_2464_, v_a_2472_);
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2477_);
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v_b_2463_);
v_a_2482_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2471_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2471_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2490_, lean_object* v_post_2491_, lean_object* v_usedLetOnly_2492_, lean_object* v_skipConstInApp_2493_, lean_object* v_skipInstances_2494_, lean_object* v___x_2495_, lean_object* v___y_2496_, lean_object* v_b_2497_, lean_object* v_a_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v_usedLetOnly_boxed_2505_; uint8_t v_skipConstInApp_boxed_2506_; uint8_t v_skipInstances_boxed_2507_; lean_object* v_res_2508_; 
v_usedLetOnly_boxed_2505_ = lean_unbox(v_usedLetOnly_2492_);
v_skipConstInApp_boxed_2506_ = lean_unbox(v_skipConstInApp_2493_);
v_skipInstances_boxed_2507_ = lean_unbox(v_skipInstances_2494_);
v_res_2508_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2490_, v_post_2491_, v_usedLetOnly_boxed_2505_, v_skipConstInApp_boxed_2506_, v_skipInstances_boxed_2507_, v___x_2495_, v___y_2496_, v_b_2497_, v_a_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v_a_2498_);
lean_dec(v___y_2496_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2509_, lean_object* v___x_2510_, lean_object* v_pre_2511_, lean_object* v_post_2512_, uint8_t v_usedLetOnly_2513_, uint8_t v_skipConstInApp_2514_, uint8_t v_skipInstances_2515_, lean_object* v_a_2516_, lean_object* v_b_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___y_2526_; uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_lt(v_a_2516_, v_upperBound_2509_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_dec(v_a_2516_);
lean_dec_ref(v_post_2512_);
lean_dec_ref(v_pre_2511_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_b_2517_);
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2551_ = lean_array_fget_borrowed(v_b_2517_, v_a_2516_);
v___x_2552_ = lean_array_get_size(v___x_2510_);
v___x_2553_ = lean_nat_dec_lt(v_a_2516_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; 
lean_inc(v___x_2551_);
v___x_2554_ = lean_box(v_usedLetOnly_2513_);
v___x_2555_ = lean_box(v_skipConstInApp_2514_);
v___x_2556_ = lean_box(v_skipInstances_2515_);
lean_inc(v_a_2516_);
lean_inc(v___y_2518_);
lean_inc_ref(v_post_2512_);
lean_inc_ref(v_pre_2511_);
v___f_2557_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2557_, 0, v_pre_2511_);
lean_closure_set(v___f_2557_, 1, v_post_2512_);
lean_closure_set(v___f_2557_, 2, v___x_2554_);
lean_closure_set(v___f_2557_, 3, v___x_2555_);
lean_closure_set(v___f_2557_, 4, v___x_2556_);
lean_closure_set(v___f_2557_, 5, v___x_2551_);
lean_closure_set(v___f_2557_, 6, v___y_2518_);
lean_closure_set(v___f_2557_, 7, v_b_2517_);
lean_closure_set(v___f_2557_, 8, v_a_2516_);
v___y_2526_ = v___f_2557_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2558_; uint8_t v_isInstance_2559_; 
v___x_2558_ = lean_array_fget_borrowed(v___x_2510_, v_a_2516_);
v_isInstance_2559_ = lean_ctor_get_uint8(v___x_2558_, sizeof(void*)*1 + 4);
if (v_isInstance_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; 
lean_inc(v___x_2551_);
v___x_2560_ = lean_box(v_usedLetOnly_2513_);
v___x_2561_ = lean_box(v_skipConstInApp_2514_);
v___x_2562_ = lean_box(v_skipInstances_2515_);
lean_inc(v_a_2516_);
lean_inc(v___y_2518_);
lean_inc_ref(v_post_2512_);
lean_inc_ref(v_pre_2511_);
v___f_2563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2563_, 0, v_pre_2511_);
lean_closure_set(v___f_2563_, 1, v_post_2512_);
lean_closure_set(v___f_2563_, 2, v___x_2560_);
lean_closure_set(v___f_2563_, 3, v___x_2561_);
lean_closure_set(v___f_2563_, 4, v___x_2562_);
lean_closure_set(v___f_2563_, 5, v___x_2551_);
lean_closure_set(v___f_2563_, 6, v___y_2518_);
lean_closure_set(v___f_2563_, 7, v_b_2517_);
lean_closure_set(v___f_2563_, 8, v_a_2516_);
v___y_2526_ = v___f_2563_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2564_; lean_object* v___f_2565_; 
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_b_2517_);
v___f_2565_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2565_, 0, v___x_2564_);
v___y_2526_ = v___f_2565_;
goto v___jp_2525_;
}
}
}
v___jp_2525_:
{
lean_object* v___x_2527_; 
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
v___x_2527_ = lean_apply_6(v___y_2526_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, lean_box(0));
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2540_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2540_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2540_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
if (lean_obj_tag(v_a_2528_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; 
lean_dec(v_a_2516_);
lean_dec_ref(v_post_2512_);
lean_dec_ref(v_pre_2511_);
v_a_2532_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v_a_2528_, 1);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v_a_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_del_object(v___x_2530_);
v_a_2536_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v_a_2528_, 1);
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = lean_nat_add(v_a_2516_, v___x_2537_);
lean_dec(v_a_2516_);
v_a_2516_ = v___x_2538_;
v_b_2517_ = v_a_2536_;
goto _start;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2516_);
lean_dec_ref(v_post_2512_);
lean_dec_ref(v_pre_2511_);
v_a_2541_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2527_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2527_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2566_, lean_object* v_pre_2567_, lean_object* v_post_2568_, uint8_t v_usedLetOnly_2569_, uint8_t v_skipConstInApp_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_f_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; 
if (lean_obj_tag(v_x_2571_) == 5)
{
lean_object* v_fn_2631_; lean_object* v_arg_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_fn_2631_ = lean_ctor_get(v_x_2571_, 0);
lean_inc_ref(v_fn_2631_);
v_arg_2632_ = lean_ctor_get(v_x_2571_, 1);
lean_inc_ref(v_arg_2632_);
lean_dec_ref_known(v_x_2571_, 2);
v___x_2633_ = lean_array_set(v_x_2572_, v_x_2573_, v_arg_2632_);
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_sub(v_x_2573_, v___x_2634_);
lean_dec(v_x_2573_);
v_x_2571_ = v_fn_2631_;
v_x_2572_ = v___x_2633_;
v_x_2573_ = v___x_2635_;
goto _start;
}
else
{
lean_dec(v_x_2573_);
if (v_skipConstInApp_2570_ == 0)
{
goto v___jp_2628_;
}
else
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Expr_isConst(v_x_2571_);
if (v___x_2637_ == 0)
{
goto v___jp_2628_;
}
else
{
v_f_2582_ = v_x_2571_;
v___y_2583_ = v___y_2574_;
v___y_2584_ = v___y_2575_;
v___y_2585_ = v___y_2576_;
v___y_2586_ = v___y_2577_;
v___y_2587_ = v___y_2578_;
v___y_2588_ = v___y_2579_;
goto v___jp_2581_;
}
}
}
v___jp_2581_:
{
if (v_skipInstances_2566_ == 0)
{
size_t v_sz_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v_sz_2589_ = lean_array_size(v_x_2572_);
v___x_2590_ = ((size_t)0ULL);
lean_inc_ref(v_post_2568_);
lean_inc_ref(v_pre_2567_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2567_, v_post_2568_, v_usedLetOnly_2569_, v_skipConstInApp_2570_, v_skipInstances_2566_, v_sz_2589_, v___x_2590_, v_x_2572_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_mkAppN(v_f_2582_, v_a_2592_);
lean_dec(v_a_2592_);
v___x_2594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2567_, v_post_2568_, v_usedLetOnly_2569_, v_skipConstInApp_2570_, v_skipInstances_2566_, v___x_2593_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2594_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_f_2582_);
lean_dec_ref(v_post_2568_);
lean_dec_ref(v_pre_2567_);
v_a_2595_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2591_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2591_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_array_get_size(v_x_2572_);
lean_inc_ref(v_f_2582_);
v___x_2604_ = l_Lean_Meta_getFunInfoNArgs(v_f_2582_, v___x_2603_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v_paramInfo_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_paramInfo_2606_ = lean_ctor_get(v_a_2605_, 0);
lean_inc_ref(v_paramInfo_2606_);
lean_dec(v_a_2605_);
v___x_2607_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2568_);
lean_inc_ref(v_pre_2567_);
v___x_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2603_, v_paramInfo_2606_, v_pre_2567_, v_post_2568_, v_usedLetOnly_2569_, v_skipConstInApp_2570_, v_skipInstances_2566_, v___x_2607_, v_x_2572_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec_ref(v_paramInfo_2606_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = l_Lean_mkAppN(v_f_2582_, v_a_2609_);
lean_dec(v_a_2609_);
v___x_2611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2567_, v_post_2568_, v_usedLetOnly_2569_, v_skipConstInApp_2570_, v_skipInstances_2566_, v___x_2610_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2611_;
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_f_2582_);
lean_dec_ref(v_post_2568_);
lean_dec_ref(v_pre_2567_);
v_a_2612_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2608_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2608_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_f_2582_);
lean_dec_ref(v_x_2572_);
lean_dec_ref(v_post_2568_);
lean_dec_ref(v_pre_2567_);
v_a_2620_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2604_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2604_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
v___jp_2628_:
{
lean_object* v___x_2629_; 
lean_inc_ref(v_post_2568_);
lean_inc_ref(v_pre_2567_);
v___x_2629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2567_, v_post_2568_, v_usedLetOnly_2569_, v_skipConstInApp_2570_, v_skipInstances_2566_, v_x_2571_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v_f_2582_ = v_a_2630_;
v___y_2583_ = v___y_2574_;
v___y_2584_ = v___y_2575_;
v___y_2585_ = v___y_2576_;
v___y_2586_ = v___y_2577_;
v___y_2587_ = v___y_2578_;
v___y_2588_ = v___y_2579_;
goto v___jp_2581_;
}
else
{
lean_dec_ref(v_x_2572_);
lean_dec_ref(v_post_2568_);
lean_dec_ref(v_pre_2567_);
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2638_, lean_object* v_pre_2639_, lean_object* v_e_2640_, lean_object* v_post_2641_, uint8_t v_usedLetOnly_2642_, uint8_t v_skipConstInApp_2643_, uint8_t v_skipInstances_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Core_checkSystem(v___x_2638_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref_known(v___x_2652_, 1);
lean_inc_ref(v_pre_2639_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc_ref(v_e_2640_);
v___x_2653_ = lean_apply_7(v_pre_2639_, v_e_2640_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2702_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2702_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2702_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___y_2659_; 
switch(lean_obj_tag(v_a_2654_))
{
case 0:
{
lean_object* v_e_2694_; lean_object* v___x_2696_; 
lean_dec_ref(v_post_2641_);
lean_dec_ref(v_e_2640_);
lean_dec_ref(v_pre_2639_);
v_e_2694_ = lean_ctor_get(v_a_2654_, 0);
lean_inc_ref(v_e_2694_);
lean_dec_ref_known(v_a_2654_, 1);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v_e_2694_);
v___x_2696_ = v___x_2656_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_e_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
case 1:
{
lean_object* v_e_2698_; lean_object* v___x_2699_; 
lean_del_object(v___x_2656_);
lean_dec_ref(v_e_2640_);
v_e_2698_ = lean_ctor_get(v_a_2654_, 0);
lean_inc_ref(v_e_2698_);
lean_dec_ref_known(v_a_2654_, 1);
v___x_2699_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v_e_2698_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2699_;
}
default: 
{
lean_object* v_e_x3f_2700_; 
lean_del_object(v___x_2656_);
v_e_x3f_2700_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_e_x3f_2700_);
lean_dec_ref_known(v_a_2654_, 1);
if (lean_obj_tag(v_e_x3f_2700_) == 0)
{
v___y_2659_ = v_e_2640_;
goto v___jp_2658_;
}
else
{
lean_object* v_val_2701_; 
lean_dec_ref(v_e_2640_);
v_val_2701_ = lean_ctor_get(v_e_x3f_2700_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v_e_x3f_2700_, 1);
v___y_2659_ = v_val_2701_;
goto v___jp_2658_;
}
}
}
v___jp_2658_:
{
switch(lean_obj_tag(v___y_2659_))
{
case 7:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___x_2660_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2661_;
}
case 6:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___x_2662_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2663_;
}
case 8:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___x_2664_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2665_;
}
case 5:
{
lean_object* v_dummy_2666_; lean_object* v_nargs_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_dummy_2666_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2667_ = l_Lean_Expr_getAppNumArgs(v___y_2659_);
lean_inc(v_nargs_2667_);
v___x_2668_ = lean_mk_array(v_nargs_2667_, v_dummy_2666_);
v___x_2669_ = lean_unsigned_to_nat(1u);
v___x_2670_ = lean_nat_sub(v_nargs_2667_, v___x_2669_);
lean_dec(v_nargs_2667_);
v___x_2671_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2644_, v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v___y_2659_, v___x_2668_, v___x_2670_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2671_;
}
case 10:
{
lean_object* v_data_2672_; lean_object* v_expr_2673_; lean_object* v___x_2674_; 
v_data_2672_ = lean_ctor_get(v___y_2659_, 0);
v_expr_2673_ = lean_ctor_get(v___y_2659_, 1);
lean_inc_ref(v_expr_2673_);
lean_inc_ref(v_post_2641_);
lean_inc_ref(v_pre_2639_);
v___x_2674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v_expr_2673_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; size_t v___x_2676_; size_t v___x_2677_; uint8_t v___x_2678_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_ptr_addr(v_expr_2673_);
v___x_2677_ = lean_ptr_addr(v_a_2675_);
v___x_2678_ = lean_usize_dec_eq(v___x_2676_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_inc(v_data_2672_);
lean_dec_ref_known(v___y_2659_, 2);
v___x_2679_ = l_Lean_Expr_mdata___override(v_data_2672_, v_a_2675_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___x_2679_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2680_;
}
else
{
lean_object* v___x_2681_; 
lean_dec(v_a_2675_);
v___x_2681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2681_;
}
}
else
{
lean_dec_ref_known(v___y_2659_, 2);
lean_dec_ref(v_post_2641_);
lean_dec_ref(v_pre_2639_);
return v___x_2674_;
}
}
case 11:
{
lean_object* v_typeName_2682_; lean_object* v_idx_2683_; lean_object* v_struct_2684_; lean_object* v___x_2685_; 
v_typeName_2682_ = lean_ctor_get(v___y_2659_, 0);
v_idx_2683_ = lean_ctor_get(v___y_2659_, 1);
v_struct_2684_ = lean_ctor_get(v___y_2659_, 2);
lean_inc_ref(v_struct_2684_);
lean_inc_ref(v_post_2641_);
lean_inc_ref(v_pre_2639_);
v___x_2685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v_struct_2684_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; size_t v___x_2687_; size_t v___x_2688_; uint8_t v___x_2689_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = lean_ptr_addr(v_struct_2684_);
v___x_2688_ = lean_ptr_addr(v_a_2686_);
v___x_2689_ = lean_usize_dec_eq(v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_inc(v_idx_2683_);
lean_inc(v_typeName_2682_);
lean_dec_ref_known(v___y_2659_, 3);
v___x_2690_ = l_Lean_Expr_proj___override(v_typeName_2682_, v_idx_2683_, v_a_2686_);
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___x_2690_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; 
lean_dec(v_a_2686_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2692_;
}
}
else
{
lean_dec_ref_known(v___y_2659_, 3);
lean_dec_ref(v_post_2641_);
lean_dec_ref(v_pre_2639_);
return v___x_2685_;
}
}
default: 
{
lean_object* v___x_2693_; 
v___x_2693_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2639_, v_post_2641_, v_usedLetOnly_2642_, v_skipConstInApp_2643_, v_skipInstances_2644_, v___y_2659_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2693_;
}
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_post_2641_);
lean_dec_ref(v_e_2640_);
lean_dec_ref(v_pre_2639_);
v_a_2703_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2653_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2653_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_post_2641_);
lean_dec_ref(v_e_2640_);
lean_dec_ref(v_pre_2639_);
v_a_2711_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2652_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2652_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2719_, lean_object* v_pre_2720_, lean_object* v_e_2721_, lean_object* v_post_2722_, lean_object* v_usedLetOnly_2723_, lean_object* v_skipConstInApp_2724_, lean_object* v_skipInstances_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v_usedLetOnly_boxed_2733_; uint8_t v_skipConstInApp_boxed_2734_; uint8_t v_skipInstances_boxed_2735_; lean_object* v_res_2736_; 
v_usedLetOnly_boxed_2733_ = lean_unbox(v_usedLetOnly_2723_);
v_skipConstInApp_boxed_2734_ = lean_unbox(v_skipConstInApp_2724_);
v_skipInstances_boxed_2735_ = lean_unbox(v_skipInstances_2725_);
v_res_2736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2719_, v_pre_2720_, v_e_2721_, v_post_2722_, v_usedLetOnly_boxed_2733_, v_skipConstInApp_boxed_2734_, v_skipInstances_boxed_2735_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2737_, lean_object* v_post_2738_, uint8_t v_usedLetOnly_2739_, uint8_t v_skipConstInApp_2740_, uint8_t v_skipInstances_2741_, lean_object* v_e_2742_, lean_object* v_a_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_inc(v_a_2743_);
v___x_2750_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2750_, 0, lean_box(0));
lean_closure_set(v___x_2750_, 1, lean_box(0));
lean_closure_set(v___x_2750_, 2, v_a_2743_);
v___x_2751_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2750_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2786_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2786_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2786_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2752_, v_e_2742_);
lean_dec(v_a_2752_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; 
lean_del_object(v___x_2754_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2758_ = lean_box(v_usedLetOnly_2739_);
v___x_2759_ = lean_box(v_skipConstInApp_2740_);
v___x_2760_ = lean_box(v_skipInstances_2741_);
lean_inc_ref(v_e_2742_);
v___f_2761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2761_, 0, v___x_2757_);
lean_closure_set(v___f_2761_, 1, v_pre_2737_);
lean_closure_set(v___f_2761_, 2, v_e_2742_);
lean_closure_set(v___f_2761_, 3, v_post_2738_);
lean_closure_set(v___f_2761_, 4, v___x_2758_);
lean_closure_set(v___f_2761_, 5, v___x_2759_);
lean_closure_set(v___f_2761_, 6, v___x_2760_);
v___x_2762_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2761_, v_a_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_n(v_a_2763_, 2);
lean_dec_ref_known(v___x_2762_, 1);
lean_inc(v_a_2743_);
v___f_2764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2764_, 0, v_a_2743_);
lean_closure_set(v___f_2764_, 1, v_e_2742_);
lean_closure_set(v___f_2764_, 2, v_a_2763_);
v___x_2765_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2764_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v___x_2765_, 0);
lean_dec(v_unused_2773_);
v___x_2767_ = v___x_2765_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_dec(v___x_2765_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2763_);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2763_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2763_);
v_a_2774_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2765_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2765_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_dec_ref(v_e_2742_);
return v___x_2762_;
}
}
else
{
lean_object* v_val_2782_; lean_object* v___x_2784_; 
lean_dec_ref(v_e_2742_);
lean_dec_ref(v_post_2738_);
lean_dec_ref(v_pre_2737_);
v_val_2782_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_val_2782_);
lean_dec_ref_known(v___x_2756_, 1);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_val_2782_);
v___x_2784_ = v___x_2754_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_val_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_e_2742_);
lean_dec_ref(v_post_2738_);
lean_dec_ref(v_pre_2737_);
v_a_2787_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2751_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2751_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2795_, lean_object* v_post_2796_, uint8_t v_usedLetOnly_2797_, uint8_t v_skipConstInApp_2798_, uint8_t v_skipInstances_2799_, lean_object* v_fvars_2800_, lean_object* v_e_2801_, lean_object* v_a_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
if (lean_obj_tag(v_e_2801_) == 7)
{
lean_object* v_binderName_2809_; lean_object* v_binderType_2810_; lean_object* v_body_2811_; uint8_t v_binderInfo_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_binderName_2809_ = lean_ctor_get(v_e_2801_, 0);
lean_inc(v_binderName_2809_);
v_binderType_2810_ = lean_ctor_get(v_e_2801_, 1);
lean_inc_ref(v_binderType_2810_);
v_body_2811_ = lean_ctor_get(v_e_2801_, 2);
lean_inc_ref(v_body_2811_);
v_binderInfo_2812_ = lean_ctor_get_uint8(v_e_2801_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2801_, 3);
v___x_2813_ = lean_box(v_usedLetOnly_2797_);
v___x_2814_ = lean_box(v_skipConstInApp_2798_);
v___x_2815_ = lean_box(v_skipInstances_2799_);
lean_inc_ref(v_post_2796_);
lean_inc_ref(v_pre_2795_);
lean_inc_ref(v_fvars_2800_);
v___f_2816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2816_, 0, v_fvars_2800_);
lean_closure_set(v___f_2816_, 1, v_pre_2795_);
lean_closure_set(v___f_2816_, 2, v_post_2796_);
lean_closure_set(v___f_2816_, 3, v___x_2813_);
lean_closure_set(v___f_2816_, 4, v___x_2814_);
lean_closure_set(v___f_2816_, 5, v___x_2815_);
lean_closure_set(v___f_2816_, 6, v_body_2811_);
v___x_2817_ = lean_expr_instantiate_rev(v_binderType_2810_, v_fvars_2800_);
lean_dec_ref(v_fvars_2800_);
lean_dec_ref(v_binderType_2810_);
v___x_2818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2795_, v_post_2796_, v_usedLetOnly_2797_, v_skipConstInApp_2798_, v_skipInstances_2799_, v___x_2817_, v_a_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = 0;
v___x_2821_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2809_, v_binderInfo_2812_, v_a_2819_, v___f_2816_, v___x_2820_, v_a_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2821_;
}
else
{
lean_dec_ref(v___f_2816_);
lean_dec(v_binderName_2809_);
return v___x_2818_;
}
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_expr_instantiate_rev(v_e_2801_, v_fvars_2800_);
lean_dec_ref(v_e_2801_);
lean_inc_ref(v_post_2796_);
lean_inc_ref(v_pre_2795_);
v___x_2823_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2795_, v_post_2796_, v_usedLetOnly_2797_, v_skipConstInApp_2798_, v_skipInstances_2799_, v___x_2822_, v_a_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; uint8_t v___x_2825_; uint8_t v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = 0;
v___x_2826_ = 1;
v___x_2827_ = 1;
v___x_2828_ = l_Lean_Meta_mkForallFVars(v_fvars_2800_, v_a_2824_, v___x_2825_, v_usedLetOnly_2797_, v___x_2826_, v___x_2827_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec_ref(v_fvars_2800_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2795_, v_post_2796_, v_usedLetOnly_2797_, v_skipConstInApp_2798_, v_skipInstances_2799_, v_a_2829_, v_a_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2830_;
}
else
{
lean_dec_ref(v_post_2796_);
lean_dec_ref(v_pre_2795_);
return v___x_2828_;
}
}
else
{
lean_dec_ref(v_fvars_2800_);
lean_dec_ref(v_post_2796_);
lean_dec_ref(v_pre_2795_);
return v___x_2823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2831_, lean_object* v_pre_2832_, lean_object* v_post_2833_, uint8_t v_usedLetOnly_2834_, uint8_t v_skipConstInApp_2835_, uint8_t v_skipInstances_2836_, lean_object* v_body_2837_, lean_object* v_x_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_array_push(v_fvars_2831_, v_x_2838_);
v___x_2847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2832_, v_post_2833_, v_usedLetOnly_2834_, v_skipConstInApp_2835_, v_skipInstances_2836_, v___x_2846_, v_body_2837_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2848_, lean_object* v_post_2849_, lean_object* v_usedLetOnly_2850_, lean_object* v_skipConstInApp_2851_, lean_object* v_skipInstances_2852_, lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v_usedLetOnly_boxed_2861_; uint8_t v_skipConstInApp_boxed_2862_; uint8_t v_skipInstances_boxed_2863_; lean_object* v_res_2864_; 
v_usedLetOnly_boxed_2861_ = lean_unbox(v_usedLetOnly_2850_);
v_skipConstInApp_boxed_2862_ = lean_unbox(v_skipConstInApp_2851_);
v_skipInstances_boxed_2863_ = lean_unbox(v_skipInstances_2852_);
v_res_2864_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2848_, v_post_2849_, v_usedLetOnly_boxed_2861_, v_skipConstInApp_boxed_2862_, v_skipInstances_boxed_2863_, v_e_2853_, v_a_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec(v_a_2854_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2865_, lean_object* v_post_2866_, lean_object* v_usedLetOnly_2867_, lean_object* v_skipConstInApp_2868_, lean_object* v_skipInstances_2869_, lean_object* v_sz_2870_, lean_object* v_i_2871_, lean_object* v_bs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v_usedLetOnly_boxed_2880_; uint8_t v_skipConstInApp_boxed_2881_; uint8_t v_skipInstances_boxed_2882_; size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_usedLetOnly_boxed_2880_ = lean_unbox(v_usedLetOnly_2867_);
v_skipConstInApp_boxed_2881_ = lean_unbox(v_skipConstInApp_2868_);
v_skipInstances_boxed_2882_ = lean_unbox(v_skipInstances_2869_);
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2870_);
lean_dec(v_sz_2870_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2865_, v_post_2866_, v_usedLetOnly_boxed_2880_, v_skipConstInApp_boxed_2881_, v_skipInstances_boxed_2882_, v_sz_boxed_2883_, v_i_boxed_2884_, v_bs_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2886_, lean_object* v_post_2887_, lean_object* v_usedLetOnly_2888_, lean_object* v_skipConstInApp_2889_, lean_object* v_skipInstances_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v_usedLetOnly_boxed_2899_; uint8_t v_skipConstInApp_boxed_2900_; uint8_t v_skipInstances_boxed_2901_; lean_object* v_res_2902_; 
v_usedLetOnly_boxed_2899_ = lean_unbox(v_usedLetOnly_2888_);
v_skipConstInApp_boxed_2900_ = lean_unbox(v_skipConstInApp_2889_);
v_skipInstances_boxed_2901_ = lean_unbox(v_skipInstances_2890_);
v_res_2902_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2886_, v_post_2887_, v_usedLetOnly_boxed_2899_, v_skipConstInApp_boxed_2900_, v_skipInstances_boxed_2901_, v_e_2891_, v_a_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec(v_a_2892_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2903_, lean_object* v_post_2904_, lean_object* v_usedLetOnly_2905_, lean_object* v_skipConstInApp_2906_, lean_object* v_skipInstances_2907_, lean_object* v_fvars_2908_, lean_object* v_e_2909_, lean_object* v_a_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v_usedLetOnly_boxed_2917_; uint8_t v_skipConstInApp_boxed_2918_; uint8_t v_skipInstances_boxed_2919_; lean_object* v_res_2920_; 
v_usedLetOnly_boxed_2917_ = lean_unbox(v_usedLetOnly_2905_);
v_skipConstInApp_boxed_2918_ = lean_unbox(v_skipConstInApp_2906_);
v_skipInstances_boxed_2919_ = lean_unbox(v_skipInstances_2907_);
v_res_2920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2903_, v_post_2904_, v_usedLetOnly_boxed_2917_, v_skipConstInApp_boxed_2918_, v_skipInstances_boxed_2919_, v_fvars_2908_, v_e_2909_, v_a_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v_a_2910_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2921_, lean_object* v_post_2922_, lean_object* v_usedLetOnly_2923_, lean_object* v_skipConstInApp_2924_, lean_object* v_skipInstances_2925_, lean_object* v_fvars_2926_, lean_object* v_e_2927_, lean_object* v_a_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v_usedLetOnly_boxed_2935_; uint8_t v_skipConstInApp_boxed_2936_; uint8_t v_skipInstances_boxed_2937_; lean_object* v_res_2938_; 
v_usedLetOnly_boxed_2935_ = lean_unbox(v_usedLetOnly_2923_);
v_skipConstInApp_boxed_2936_ = lean_unbox(v_skipConstInApp_2924_);
v_skipInstances_boxed_2937_ = lean_unbox(v_skipInstances_2925_);
v_res_2938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2921_, v_post_2922_, v_usedLetOnly_boxed_2935_, v_skipConstInApp_boxed_2936_, v_skipInstances_boxed_2937_, v_fvars_2926_, v_e_2927_, v_a_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_a_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2939_, lean_object* v_post_2940_, lean_object* v_usedLetOnly_2941_, lean_object* v_skipConstInApp_2942_, lean_object* v_skipInstances_2943_, lean_object* v_fvars_2944_, lean_object* v_e_2945_, lean_object* v_a_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v_usedLetOnly_boxed_2953_; uint8_t v_skipConstInApp_boxed_2954_; uint8_t v_skipInstances_boxed_2955_; lean_object* v_res_2956_; 
v_usedLetOnly_boxed_2953_ = lean_unbox(v_usedLetOnly_2941_);
v_skipConstInApp_boxed_2954_ = lean_unbox(v_skipConstInApp_2942_);
v_skipInstances_boxed_2955_ = lean_unbox(v_skipInstances_2943_);
v_res_2956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2939_, v_post_2940_, v_usedLetOnly_boxed_2953_, v_skipConstInApp_boxed_2954_, v_skipInstances_boxed_2955_, v_fvars_2944_, v_e_2945_, v_a_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec(v_a_2946_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2957_, lean_object* v___x_2958_, lean_object* v_pre_2959_, lean_object* v_post_2960_, lean_object* v_usedLetOnly_2961_, lean_object* v_skipConstInApp_2962_, lean_object* v_skipInstances_2963_, lean_object* v_a_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v_usedLetOnly_boxed_2973_; uint8_t v_skipConstInApp_boxed_2974_; uint8_t v_skipInstances_boxed_2975_; lean_object* v_res_2976_; 
v_usedLetOnly_boxed_2973_ = lean_unbox(v_usedLetOnly_2961_);
v_skipConstInApp_boxed_2974_ = lean_unbox(v_skipConstInApp_2962_);
v_skipInstances_boxed_2975_ = lean_unbox(v_skipInstances_2963_);
v_res_2976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2957_, v___x_2958_, v_pre_2959_, v_post_2960_, v_usedLetOnly_boxed_2973_, v_skipConstInApp_boxed_2974_, v_skipInstances_boxed_2975_, v_a_2964_, v_b_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___x_2958_);
lean_dec(v_upperBound_2957_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2977_, lean_object* v_pre_2978_, lean_object* v_post_2979_, lean_object* v_usedLetOnly_2980_, lean_object* v_skipConstInApp_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v_skipInstances_boxed_2992_; uint8_t v_usedLetOnly_boxed_2993_; uint8_t v_skipConstInApp_boxed_2994_; lean_object* v_res_2995_; 
v_skipInstances_boxed_2992_ = lean_unbox(v_skipInstances_2977_);
v_usedLetOnly_boxed_2993_ = lean_unbox(v_usedLetOnly_2980_);
v_skipConstInApp_boxed_2994_ = lean_unbox(v_skipConstInApp_2981_);
v_res_2995_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2992_, v_pre_2978_, v_post_2979_, v_usedLetOnly_boxed_2993_, v_skipConstInApp_boxed_2994_, v_x_2982_, v_x_2983_, v_x_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_apply_1(v_x_2997_, lean_box(0));
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_x_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3006_, v_x_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
return v_res_3014_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_unsigned_to_nat(16u);
v___x_3017_ = lean_mk_array(v___x_3016_, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3018_);
return v___x_3020_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3022_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3022_, 0, lean_box(0));
lean_closure_set(v___x_3022_, 1, lean_box(0));
lean_closure_set(v___x_3022_, 2, v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3023_, lean_object* v_pre_3024_, lean_object* v_post_3025_, uint8_t v_usedLetOnly_3026_, uint8_t v_skipConstInApp_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v_a_3037_; lean_object* v___x_3038_; 
v___x_3034_ = 0;
v___x_3035_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3036_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3035_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3036_);
v___x_3038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3024_, v_post_3025_, v_usedLetOnly_3026_, v_skipConstInApp_3027_, v___x_3034_, v_input_3023_, v_a_3037_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3040_, 0, lean_box(0));
lean_closure_set(v___x_3040_, 1, lean_box(0));
lean_closure_set(v___x_3040_, 2, v_a_3037_);
v___x_3041_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3040_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3041_, 0);
lean_dec(v_unused_3049_);
v___x_3043_ = v___x_3041_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v___x_3041_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v_a_3039_);
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3039_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_dec(v_a_3037_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3050_, lean_object* v_pre_3051_, lean_object* v_post_3052_, lean_object* v_usedLetOnly_3053_, lean_object* v_skipConstInApp_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
uint8_t v_usedLetOnly_boxed_3061_; uint8_t v_skipConstInApp_boxed_3062_; lean_object* v_res_3063_; 
v_usedLetOnly_boxed_3061_ = lean_unbox(v_usedLetOnly_3053_);
v_skipConstInApp_boxed_3062_ = lean_unbox(v_skipConstInApp_3054_);
v_res_3063_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3050_, v_pre_3051_, v_post_3052_, v_usedLetOnly_boxed_3061_, v_skipConstInApp_boxed_3062_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3065_, uint8_t v_elimTrivial_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v_pre_3073_; lean_object* v___f_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3072_ = lean_box(v_elimTrivial_3066_);
v_pre_3073_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3073_, 0, v___x_3072_);
v___f_3074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3075_ = 0;
v___x_3076_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_3077_ = lean_st_mk_ref(v___x_3076_);
v___x_3078_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3065_, v_pre_3073_, v___f_3074_, v___x_3075_, v___x_3075_, v___x_3077_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3087_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3087_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = lean_st_ref_get(v___x_3077_);
lean_dec(v___x_3077_);
lean_dec(v___x_3083_);
if (v_isShared_3082_ == 0)
{
v___x_3085_ = v___x_3081_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3079_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
lean_dec(v___x_3077_);
return v___x_3078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3088_, lean_object* v_elimTrivial_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
uint8_t v_elimTrivial_boxed_3095_; lean_object* v_res_3096_; 
v_elimTrivial_boxed_3095_ = lean_unbox(v_elimTrivial_3089_);
v_res_3096_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3088_, v_elimTrivial_boxed_3095_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3097_, lean_object* v___x_3098_, lean_object* v_pre_3099_, lean_object* v_post_3100_, uint8_t v_usedLetOnly_3101_, uint8_t v_skipConstInApp_3102_, uint8_t v_skipInstances_3103_, lean_object* v___x_3104_, lean_object* v_inst_3105_, lean_object* v_R_3106_, lean_object* v_a_3107_, lean_object* v_b_3108_, lean_object* v_c_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3097_, v___x_3098_, v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3103_, v_a_3107_, v_b_3108_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3118_ = _args[0];
lean_object* v___x_3119_ = _args[1];
lean_object* v_pre_3120_ = _args[2];
lean_object* v_post_3121_ = _args[3];
lean_object* v_usedLetOnly_3122_ = _args[4];
lean_object* v_skipConstInApp_3123_ = _args[5];
lean_object* v_skipInstances_3124_ = _args[6];
lean_object* v___x_3125_ = _args[7];
lean_object* v_inst_3126_ = _args[8];
lean_object* v_R_3127_ = _args[9];
lean_object* v_a_3128_ = _args[10];
lean_object* v_b_3129_ = _args[11];
lean_object* v_c_3130_ = _args[12];
lean_object* v___y_3131_ = _args[13];
lean_object* v___y_3132_ = _args[14];
lean_object* v___y_3133_ = _args[15];
lean_object* v___y_3134_ = _args[16];
lean_object* v___y_3135_ = _args[17];
lean_object* v___y_3136_ = _args[18];
lean_object* v___y_3137_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3138_; uint8_t v_skipConstInApp_boxed_3139_; uint8_t v_skipInstances_boxed_3140_; lean_object* v_res_3141_; 
v_usedLetOnly_boxed_3138_ = lean_unbox(v_usedLetOnly_3122_);
v_skipConstInApp_boxed_3139_ = lean_unbox(v_skipConstInApp_3123_);
v_skipInstances_boxed_3140_ = lean_unbox(v_skipInstances_3124_);
v_res_3141_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3118_, v___x_3119_, v_pre_3120_, v_post_3121_, v_usedLetOnly_boxed_3138_, v_skipConstInApp_boxed_3139_, v_skipInstances_boxed_3140_, v___x_3125_, v_inst_3126_, v_R_3127_, v_a_3128_, v_b_3129_, v_c_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec(v___x_3125_);
lean_dec_ref(v___x_3119_);
lean_dec(v_upperBound_3118_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3142_, lean_object* v_m_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3143_, v_a_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3146_, lean_object* v_m_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3146_, v_m_3147_, v_a_3148_);
lean_dec_ref(v_a_3148_);
lean_dec_ref(v_m_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3150_, lean_object* v_name_3151_, uint8_t v_bi_3152_, lean_object* v_type_3153_, lean_object* v_k_3154_, uint8_t v_kind_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3151_, v_bi_3152_, v_type_3153_, v_k_3154_, v_kind_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_name_3165_, lean_object* v_bi_3166_, lean_object* v_type_3167_, lean_object* v_k_3168_, lean_object* v_kind_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v_bi_boxed_3177_; uint8_t v_kind_boxed_3178_; lean_object* v_res_3179_; 
v_bi_boxed_3177_ = lean_unbox(v_bi_3166_);
v_kind_boxed_3178_ = lean_unbox(v_kind_3169_);
v_res_3179_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3164_, v_name_3165_, v_bi_boxed_3177_, v_type_3167_, v_k_3168_, v_kind_boxed_3178_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v___y_3170_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3180_, lean_object* v_name_3181_, lean_object* v_type_3182_, lean_object* v_val_3183_, lean_object* v_k_3184_, uint8_t v_nondep_3185_, uint8_t v_kind_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3181_, v_type_3182_, v_val_3183_, v_k_3184_, v_nondep_3185_, v_kind_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3195_, lean_object* v_name_3196_, lean_object* v_type_3197_, lean_object* v_val_3198_, lean_object* v_k_3199_, lean_object* v_nondep_3200_, lean_object* v_kind_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_nondep_boxed_3209_; uint8_t v_kind_boxed_3210_; lean_object* v_res_3211_; 
v_nondep_boxed_3209_ = lean_unbox(v_nondep_3200_);
v_kind_boxed_3210_ = lean_unbox(v_kind_3201_);
v_res_3211_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3195_, v_name_3196_, v_type_3197_, v_val_3198_, v_k_3199_, v_nondep_boxed_3209_, v_kind_boxed_3210_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec(v___y_3202_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3212_, lean_object* v_ref_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3213_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3220_, lean_object* v_ref_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3220_, v_ref_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3228_, lean_object* v_x_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3238_, v_x_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3248_, lean_object* v_m_3249_, lean_object* v_a_3250_, lean_object* v_b_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3249_, v_a_3250_, v_b_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3253_, lean_object* v_a_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3254_, v_x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3257_, lean_object* v_a_3258_, lean_object* v_x_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3257_, v_a_3258_, v_x_3259_);
lean_dec(v_x_3259_);
lean_dec_ref(v_a_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3261_, lean_object* v_a_3262_, lean_object* v_x_3263_){
_start:
{
uint8_t v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_){
_start:
{
uint8_t v_res_3268_; lean_object* v_r_3269_; 
v_res_3268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3265_, v_a_3266_, v_x_3267_);
lean_dec(v_x_3267_);
lean_dec_ref(v_a_3266_);
v_r_3269_ = lean_box(v_res_3268_);
return v_r_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3270_, lean_object* v_data_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_b_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3274_, v_b_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3278_, lean_object* v_i_3279_, lean_object* v_source_3280_, lean_object* v_target_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3279_, v_source_3280_, v_target_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3284_, v_x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3287_, lean_object* v_x_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3287_, v_x_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_a_3303_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3294_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3294_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3311_, lean_object* v_x_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3311_, v_x_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3319_, lean_object* v_mvarId_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3320_, v_x_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3328_, lean_object* v_mvarId_3329_, lean_object* v_x_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3328_, v_mvarId_3329_, v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3337_, lean_object* v_as_3338_, size_t v_sz_3339_, size_t v_i_3340_, lean_object* v_b_3341_){
_start:
{
uint8_t v___x_3343_; 
v___x_3343_ = lean_usize_dec_lt(v_i_3340_, v_sz_3339_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_b_3341_);
return v___x_3344_;
}
else
{
lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3392_; 
v_snd_3345_ = lean_ctor_get(v_b_3341_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_b_3341_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v_b_3341_, 0);
lean_dec(v_unused_3393_);
v___x_3347_ = v_b_3341_;
v_isShared_3348_ = v_isSharedCheck_3392_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_dec(v_b_3341_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3392_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_a_3351_; lean_object* v_a_3358_; 
v___x_3349_ = lean_box(0);
v_a_3358_ = lean_array_uget_borrowed(v_as_3338_, v_i_3340_);
if (lean_obj_tag(v_a_3358_) == 0)
{
v_a_3351_ = v_snd_3345_;
goto v___jp_3350_;
}
else
{
lean_object* v_val_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3391_; 
v_val_3359_ = lean_ctor_get(v_a_3358_, 0);
v_fst_3360_ = lean_ctor_get(v_snd_3345_, 0);
v_snd_3361_ = lean_ctor_get(v_snd_3345_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_snd_3345_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3363_ = v_snd_3345_;
v_isShared_3364_ = v_isSharedCheck_3391_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_snd_3361_);
lean_inc(v_fst_3360_);
lean_dec(v_snd_3345_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3391_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
uint8_t v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = 0;
v___x_3366_ = l_Lean_LocalDecl_value_x3f(v_val_3359_, v___x_3365_);
if (lean_obj_tag(v___x_3366_) == 1)
{
lean_object* v_val_3367_; lean_object* v___x_3368_; 
v_val_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = l_Lean_LocalDecl_type(v_val_3359_);
if (lean_obj_tag(v___x_3368_) == 10)
{
lean_object* v_data_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; uint8_t v___x_3374_; 
v_data_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_data_3369_);
lean_dec_ref_known(v___x_3368_, 2);
v___x_3370_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3371_ = lean_unsigned_to_nat(2u);
v___x_3372_ = l_Lean_KVMap_getNat(v_data_3369_, v___x_3370_, v___x_3371_);
lean_dec(v_data_3369_);
v___x_3373_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3372_);
lean_dec(v___x_3372_);
v___x_3374_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3373_, v_val_3367_, v_elimTrivial_3337_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3375_ = l_Lean_LocalDecl_fvarId(v_val_3359_);
v___x_3376_ = l_Lean_mkFVar(v___x_3375_);
v___x_3377_ = lean_array_push(v_fst_3360_, v___x_3376_);
v___x_3378_ = lean_array_push(v_snd_3361_, v_val_3367_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 1, v___x_3378_);
lean_ctor_set(v___x_3363_, 0, v___x_3377_);
v___x_3380_ = v___x_3363_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3351_ = v___x_3380_;
goto v___jp_3350_;
}
}
else
{
lean_object* v___x_3383_; 
lean_dec(v_val_3367_);
if (v_isShared_3364_ == 0)
{
v___x_3383_ = v___x_3363_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_fst_3360_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_snd_3361_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_a_3351_ = v___x_3383_;
goto v___jp_3350_;
}
}
}
else
{
lean_object* v___x_3386_; 
lean_dec_ref(v___x_3368_);
lean_dec(v_val_3367_);
if (v_isShared_3364_ == 0)
{
v___x_3386_ = v___x_3363_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_fst_3360_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3361_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v_a_3351_ = v___x_3386_;
goto v___jp_3350_;
}
}
}
else
{
lean_object* v___x_3389_; 
lean_dec(v___x_3366_);
if (v_isShared_3364_ == 0)
{
v___x_3389_ = v___x_3363_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_fst_3360_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_snd_3361_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
v_a_3351_ = v___x_3389_;
goto v___jp_3350_;
}
}
}
}
v___jp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3351_);
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_a_3351_);
v___x_3353_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
size_t v___x_3354_; size_t v___x_3355_; 
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3340_, v___x_3354_);
v_i_3340_ = v___x_3355_;
v_b_3341_ = v___x_3353_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3394_, lean_object* v_as_3395_, lean_object* v_sz_3396_, lean_object* v_i_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_){
_start:
{
uint8_t v_elimTrivial_boxed_3400_; size_t v_sz_boxed_3401_; size_t v_i_boxed_3402_; lean_object* v_res_3403_; 
v_elimTrivial_boxed_3400_ = lean_unbox(v_elimTrivial_3394_);
v_sz_boxed_3401_ = lean_unbox_usize(v_sz_3396_);
lean_dec(v_sz_3396_);
v_i_boxed_3402_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_res_3403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3400_, v_as_3395_, v_sz_boxed_3401_, v_i_boxed_3402_, v_b_3398_);
lean_dec_ref(v_as_3395_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3404_, lean_object* v_as_3405_, size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
uint8_t v___x_3414_; 
v___x_3414_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_b_3408_);
return v___x_3415_;
}
else
{
lean_object* v_snd_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3463_; 
v_snd_3416_ = lean_ctor_get(v_b_3408_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_b_3408_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v_b_3408_, 0);
lean_dec(v_unused_3464_);
v___x_3418_ = v_b_3408_;
v_isShared_3419_ = v_isSharedCheck_3463_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_snd_3416_);
lean_dec(v_b_3408_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3463_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v_a_3422_; lean_object* v_a_3429_; 
v___x_3420_ = lean_box(0);
v_a_3429_ = lean_array_uget_borrowed(v_as_3405_, v_i_3407_);
if (lean_obj_tag(v_a_3429_) == 0)
{
v_a_3422_ = v_snd_3416_;
goto v___jp_3421_;
}
else
{
lean_object* v_val_3430_; lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3462_; 
v_val_3430_ = lean_ctor_get(v_a_3429_, 0);
v_fst_3431_ = lean_ctor_get(v_snd_3416_, 0);
v_snd_3432_ = lean_ctor_get(v_snd_3416_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_snd_3416_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3434_ = v_snd_3416_;
v_isShared_3435_ = v_isSharedCheck_3462_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_snd_3416_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3462_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = 0;
v___x_3437_ = l_Lean_LocalDecl_value_x3f(v_val_3430_, v___x_3436_);
if (lean_obj_tag(v___x_3437_) == 1)
{
lean_object* v_val_3438_; lean_object* v___x_3439_; 
v_val_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_val_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = l_Lean_LocalDecl_type(v_val_3430_);
if (lean_obj_tag(v___x_3439_) == 10)
{
lean_object* v_data_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; uint8_t v___x_3445_; 
v_data_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_data_3440_);
lean_dec_ref_known(v___x_3439_, 2);
v___x_3441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3442_ = lean_unsigned_to_nat(2u);
v___x_3443_ = l_Lean_KVMap_getNat(v_data_3440_, v___x_3441_, v___x_3442_);
lean_dec(v_data_3440_);
v___x_3444_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3443_);
lean_dec(v___x_3443_);
v___x_3445_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3444_, v_val_3438_, v_elimTrivial_3404_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3446_ = l_Lean_LocalDecl_fvarId(v_val_3430_);
v___x_3447_ = l_Lean_mkFVar(v___x_3446_);
v___x_3448_ = lean_array_push(v_fst_3431_, v___x_3447_);
v___x_3449_ = lean_array_push(v_snd_3432_, v_val_3438_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v___x_3449_);
lean_ctor_set(v___x_3434_, 0, v___x_3448_);
v___x_3451_ = v___x_3434_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
v_a_3422_ = v___x_3451_;
goto v___jp_3421_;
}
}
else
{
lean_object* v___x_3454_; 
lean_dec(v_val_3438_);
if (v_isShared_3435_ == 0)
{
v___x_3454_ = v___x_3434_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_snd_3432_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
v_a_3422_ = v___x_3454_;
goto v___jp_3421_;
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec_ref(v___x_3439_);
lean_dec(v_val_3438_);
if (v_isShared_3435_ == 0)
{
v___x_3457_ = v___x_3434_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3432_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
v_a_3422_ = v___x_3457_;
goto v___jp_3421_;
}
}
}
else
{
lean_object* v___x_3460_; 
lean_dec(v___x_3437_);
if (v_isShared_3435_ == 0)
{
v___x_3460_ = v___x_3434_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3431_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3432_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_a_3422_ = v___x_3460_;
goto v___jp_3421_;
}
}
}
}
v___jp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v_a_3422_);
lean_ctor_set(v___x_3418_, 0, v___x_3420_);
v___x_3424_ = v___x_3418_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_a_3422_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_add(v_i_3407_, v___x_3425_);
v___x_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3404_, v_as_3405_, v_sz_3406_, v___x_3426_, v___x_3424_);
return v___x_3427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3465_, lean_object* v_as_3466_, lean_object* v_sz_3467_, lean_object* v_i_3468_, lean_object* v_b_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v_elimTrivial_boxed_3475_; size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_elimTrivial_boxed_3475_ = lean_unbox(v_elimTrivial_3465_);
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3467_);
lean_dec(v_sz_3467_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3475_, v_as_3466_, v_sz_boxed_3476_, v_i_boxed_3477_, v_b_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_as_3466_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3479_, lean_object* v_as_3480_, size_t v_sz_3481_, size_t v_i_3482_, lean_object* v_b_3483_){
_start:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_usize_dec_lt(v_i_3482_, v_sz_3481_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v_b_3483_);
return v___x_3486_;
}
else
{
lean_object* v_snd_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3534_; 
v_snd_3487_ = lean_ctor_get(v_b_3483_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_b_3483_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v_b_3483_, 0);
lean_dec(v_unused_3535_);
v___x_3489_ = v_b_3483_;
v_isShared_3490_ = v_isSharedCheck_3534_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snd_3487_);
lean_dec(v_b_3483_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3534_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v_a_3493_; lean_object* v_a_3500_; 
v___x_3491_ = lean_box(0);
v_a_3500_ = lean_array_uget_borrowed(v_as_3480_, v_i_3482_);
if (lean_obj_tag(v_a_3500_) == 0)
{
v_a_3493_ = v_snd_3487_;
goto v___jp_3492_;
}
else
{
lean_object* v_val_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3533_; 
v_val_3501_ = lean_ctor_get(v_a_3500_, 0);
v_fst_3502_ = lean_ctor_get(v_snd_3487_, 0);
v_snd_3503_ = lean_ctor_get(v_snd_3487_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_snd_3487_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3505_ = v_snd_3487_;
v_isShared_3506_ = v_isSharedCheck_3533_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_snd_3503_);
lean_inc(v_fst_3502_);
lean_dec(v_snd_3487_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3533_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
uint8_t v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = 0;
v___x_3508_ = l_Lean_LocalDecl_value_x3f(v_val_3501_, v___x_3507_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; lean_object* v___x_3510_; 
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = l_Lean_LocalDecl_type(v_val_3501_);
if (lean_obj_tag(v___x_3510_) == 10)
{
lean_object* v_data_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; uint8_t v___x_3516_; 
v_data_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_data_3511_);
lean_dec_ref_known(v___x_3510_, 2);
v___x_3512_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3513_ = lean_unsigned_to_nat(2u);
v___x_3514_ = l_Lean_KVMap_getNat(v_data_3511_, v___x_3512_, v___x_3513_);
lean_dec(v_data_3511_);
v___x_3515_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3514_);
lean_dec(v___x_3514_);
v___x_3516_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3515_, v_val_3509_, v_elimTrivial_3479_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3517_ = l_Lean_LocalDecl_fvarId(v_val_3501_);
v___x_3518_ = l_Lean_mkFVar(v___x_3517_);
v___x_3519_ = lean_array_push(v_fst_3502_, v___x_3518_);
v___x_3520_ = lean_array_push(v_snd_3503_, v_val_3509_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3520_);
lean_ctor_set(v___x_3505_, 0, v___x_3519_);
v___x_3522_ = v___x_3505_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
v_a_3493_ = v___x_3522_;
goto v___jp_3492_;
}
}
else
{
lean_object* v___x_3525_; 
lean_dec(v_val_3509_);
if (v_isShared_3506_ == 0)
{
v___x_3525_ = v___x_3505_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_fst_3502_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_snd_3503_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
v_a_3493_ = v___x_3525_;
goto v___jp_3492_;
}
}
}
else
{
lean_object* v___x_3528_; 
lean_dec_ref(v___x_3510_);
lean_dec(v_val_3509_);
if (v_isShared_3506_ == 0)
{
v___x_3528_ = v___x_3505_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_fst_3502_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_snd_3503_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
v_a_3493_ = v___x_3528_;
goto v___jp_3492_;
}
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v___x_3508_);
if (v_isShared_3506_ == 0)
{
v___x_3531_ = v___x_3505_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_fst_3502_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_snd_3503_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_a_3493_ = v___x_3531_;
goto v___jp_3492_;
}
}
}
}
v___jp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_a_3493_);
lean_ctor_set(v___x_3489_, 0, v___x_3491_);
v___x_3495_ = v___x_3489_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_a_3493_);
v___x_3495_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
size_t v___x_3496_; size_t v___x_3497_; 
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3482_, v___x_3496_);
v_i_3482_ = v___x_3497_;
v_b_3483_ = v___x_3495_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3536_, lean_object* v_as_3537_, lean_object* v_sz_3538_, lean_object* v_i_3539_, lean_object* v_b_3540_, lean_object* v___y_3541_){
_start:
{
uint8_t v_elimTrivial_boxed_3542_; size_t v_sz_boxed_3543_; size_t v_i_boxed_3544_; lean_object* v_res_3545_; 
v_elimTrivial_boxed_3542_ = lean_unbox(v_elimTrivial_3536_);
v_sz_boxed_3543_ = lean_unbox_usize(v_sz_3538_);
lean_dec(v_sz_3538_);
v_i_boxed_3544_ = lean_unbox_usize(v_i_3539_);
lean_dec(v_i_3539_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3542_, v_as_3537_, v_sz_boxed_3543_, v_i_boxed_3544_, v_b_3540_);
lean_dec_ref(v_as_3537_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3546_, lean_object* v_as_3547_, size_t v_sz_3548_, size_t v_i_3549_, lean_object* v_b_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
uint8_t v___x_3556_; 
v___x_3556_ = lean_usize_dec_lt(v_i_3549_, v_sz_3548_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_b_3550_);
return v___x_3557_;
}
else
{
lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3605_; 
v_snd_3558_ = lean_ctor_get(v_b_3550_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_b_3550_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v_b_3550_, 0);
lean_dec(v_unused_3606_);
v___x_3560_ = v_b_3550_;
v_isShared_3561_ = v_isSharedCheck_3605_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_dec(v_b_3550_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3605_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v_a_3564_; lean_object* v_a_3571_; 
v___x_3562_ = lean_box(0);
v_a_3571_ = lean_array_uget_borrowed(v_as_3547_, v_i_3549_);
if (lean_obj_tag(v_a_3571_) == 0)
{
v_a_3564_ = v_snd_3558_;
goto v___jp_3563_;
}
else
{
lean_object* v_val_3572_; lean_object* v_fst_3573_; lean_object* v_snd_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3604_; 
v_val_3572_ = lean_ctor_get(v_a_3571_, 0);
v_fst_3573_ = lean_ctor_get(v_snd_3558_, 0);
v_snd_3574_ = lean_ctor_get(v_snd_3558_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_snd_3558_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3576_ = v_snd_3558_;
v_isShared_3577_ = v_isSharedCheck_3604_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3574_);
lean_inc(v_fst_3573_);
lean_dec(v_snd_3558_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3604_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
uint8_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = 0;
v___x_3579_ = l_Lean_LocalDecl_value_x3f(v_val_3572_, v___x_3578_);
if (lean_obj_tag(v___x_3579_) == 1)
{
lean_object* v_val_3580_; lean_object* v___x_3581_; 
v_val_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3581_ = l_Lean_LocalDecl_type(v_val_3572_);
if (lean_obj_tag(v___x_3581_) == 10)
{
lean_object* v_data_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; uint8_t v___x_3587_; 
v_data_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_data_3582_);
lean_dec_ref_known(v___x_3581_, 2);
v___x_3583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3584_ = lean_unsigned_to_nat(2u);
v___x_3585_ = l_Lean_KVMap_getNat(v_data_3582_, v___x_3583_, v___x_3584_);
lean_dec(v_data_3582_);
v___x_3586_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3585_);
lean_dec(v___x_3585_);
v___x_3587_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3586_, v_val_3580_, v_elimTrivial_3546_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3588_ = l_Lean_LocalDecl_fvarId(v_val_3572_);
v___x_3589_ = l_Lean_mkFVar(v___x_3588_);
v___x_3590_ = lean_array_push(v_fst_3573_, v___x_3589_);
v___x_3591_ = lean_array_push(v_snd_3574_, v_val_3580_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3591_);
lean_ctor_set(v___x_3576_, 0, v___x_3590_);
v___x_3593_ = v___x_3576_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
v_a_3564_ = v___x_3593_;
goto v___jp_3563_;
}
}
else
{
lean_object* v___x_3596_; 
lean_dec(v_val_3580_);
if (v_isShared_3577_ == 0)
{
v___x_3596_ = v___x_3576_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_fst_3573_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_snd_3574_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
v_a_3564_ = v___x_3596_;
goto v___jp_3563_;
}
}
}
else
{
lean_object* v___x_3599_; 
lean_dec_ref(v___x_3581_);
lean_dec(v_val_3580_);
if (v_isShared_3577_ == 0)
{
v___x_3599_ = v___x_3576_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_fst_3573_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_snd_3574_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
v_a_3564_ = v___x_3599_;
goto v___jp_3563_;
}
}
}
else
{
lean_object* v___x_3602_; 
lean_dec(v___x_3579_);
if (v_isShared_3577_ == 0)
{
v___x_3602_ = v___x_3576_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_fst_3573_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_snd_3574_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v_a_3564_ = v___x_3602_;
goto v___jp_3563_;
}
}
}
}
v___jp_3563_:
{
lean_object* v___x_3566_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v_a_3564_);
lean_ctor_set(v___x_3560_, 0, v___x_3562_);
v___x_3566_ = v___x_3560_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_a_3564_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)1ULL);
v___x_3568_ = lean_usize_add(v_i_3549_, v___x_3567_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3546_, v_as_3547_, v_sz_3548_, v___x_3568_, v___x_3566_);
return v___x_3569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3607_, lean_object* v_as_3608_, lean_object* v_sz_3609_, lean_object* v_i_3610_, lean_object* v_b_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_elimTrivial_boxed_3617_; size_t v_sz_boxed_3618_; size_t v_i_boxed_3619_; lean_object* v_res_3620_; 
v_elimTrivial_boxed_3617_ = lean_unbox(v_elimTrivial_3607_);
v_sz_boxed_3618_ = lean_unbox_usize(v_sz_3609_);
lean_dec(v_sz_3609_);
v_i_boxed_3619_ = lean_unbox_usize(v_i_3610_);
lean_dec(v_i_3610_);
v_res_3620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3617_, v_as_3608_, v_sz_boxed_3618_, v_i_boxed_3619_, v_b_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_as_3608_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3621_, uint8_t v_elimTrivial_3622_, lean_object* v_n_3623_, lean_object* v_b_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
if (lean_obj_tag(v_n_3623_) == 0)
{
lean_object* v_cs_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; size_t v_sz_3633_; size_t v___x_3634_; lean_object* v___x_3635_; 
v_cs_3630_ = lean_ctor_get(v_n_3623_, 0);
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
lean_ctor_set(v___x_3632_, 1, v_b_3624_);
v_sz_3633_ = lean_array_size(v_cs_3630_);
v___x_3634_ = ((size_t)0ULL);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3621_, v_elimTrivial_3622_, v_cs_3630_, v_sz_3633_, v___x_3634_, v___x_3632_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3650_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3650_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3650_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_fst_3640_; 
v_fst_3640_ = lean_ctor_get(v_a_3636_, 0);
if (lean_obj_tag(v_fst_3640_) == 0)
{
lean_object* v_snd_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v_snd_3641_ = lean_ctor_get(v_a_3636_, 1);
lean_inc(v_snd_3641_);
lean_dec(v_a_3636_);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_snd_3641_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3642_);
v___x_3644_ = v___x_3638_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
else
{
lean_object* v_val_3646_; lean_object* v___x_3648_; 
lean_inc_ref(v_fst_3640_);
lean_dec(v_a_3636_);
v_val_3646_ = lean_ctor_get(v_fst_3640_, 0);
lean_inc(v_val_3646_);
lean_dec_ref_known(v_fst_3640_, 1);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_val_3646_);
v___x_3648_ = v___x_3638_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_val_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
v_a_3651_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3635_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3635_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_vs_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; size_t v_sz_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v_vs_3659_ = lean_ctor_get(v_n_3623_, 0);
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v_b_3624_);
v_sz_3662_ = lean_array_size(v_vs_3659_);
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3622_, v_vs_3659_, v_sz_3662_, v___x_3663_, v___x_3661_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3679_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3679_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3679_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_fst_3669_; 
v_fst_3669_ = lean_ctor_get(v_a_3665_, 0);
if (lean_obj_tag(v_fst_3669_) == 0)
{
lean_object* v_snd_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v_snd_3670_ = lean_ctor_get(v_a_3665_, 1);
lean_inc(v_snd_3670_);
lean_dec(v_a_3665_);
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_snd_3670_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3671_);
v___x_3673_ = v___x_3667_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
else
{
lean_object* v_val_3675_; lean_object* v___x_3677_; 
lean_inc_ref(v_fst_3669_);
lean_dec(v_a_3665_);
v_val_3675_ = lean_ctor_get(v_fst_3669_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v_fst_3669_, 1);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v_val_3675_);
v___x_3677_ = v___x_3667_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_val_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3664_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3664_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3688_, uint8_t v_elimTrivial_3689_, lean_object* v_as_3690_, size_t v_sz_3691_, size_t v_i_3692_, lean_object* v_b_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = lean_usize_dec_lt(v_i_3692_, v_sz_3691_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_b_3693_);
return v___x_3700_;
}
else
{
lean_object* v_snd_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3735_; 
v_snd_3701_ = lean_ctor_get(v_b_3693_, 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_b_3693_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_b_3693_, 0);
lean_dec(v_unused_3736_);
v___x_3703_ = v_b_3693_;
v_isShared_3704_ = v_isSharedCheck_3735_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_snd_3701_);
lean_dec(v_b_3693_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3735_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v_a_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_box(0);
v_a_3706_ = lean_array_uget_borrowed(v_as_3690_, v_i_3692_);
lean_inc(v_snd_3701_);
v___x_3707_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3688_, v_elimTrivial_3689_, v_a_3706_, v_snd_3701_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3726_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3726_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3726_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
if (lean_obj_tag(v_a_3708_) == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3712_, 0, v_a_3708_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3712_);
v___x_3714_ = v___x_3703_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_snd_3701_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3714_);
v___x_3716_ = v___x_3710_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3701_);
v_a_3719_ = lean_ctor_get(v_a_3708_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v_a_3708_, 1);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 1, v_a_3719_);
lean_ctor_set(v___x_3703_, 0, v___x_3705_);
v___x_3721_ = v___x_3703_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_a_3719_);
v___x_3721_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
size_t v___x_3722_; size_t v___x_3723_; 
v___x_3722_ = ((size_t)1ULL);
v___x_3723_ = lean_usize_add(v_i_3692_, v___x_3722_);
v_i_3692_ = v___x_3723_;
v_b_3693_ = v___x_3721_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3703_);
lean_dec(v_snd_3701_);
v_a_3727_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3707_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3707_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3737_, lean_object* v_elimTrivial_3738_, lean_object* v_as_3739_, lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_b_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v_elimTrivial_boxed_3748_; size_t v_sz_boxed_3749_; size_t v_i_boxed_3750_; lean_object* v_res_3751_; 
v_elimTrivial_boxed_3748_ = lean_unbox(v_elimTrivial_3738_);
v_sz_boxed_3749_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3750_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3737_, v_elimTrivial_boxed_3748_, v_as_3739_, v_sz_boxed_3749_, v_i_boxed_3750_, v_b_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_as_3739_);
lean_dec_ref(v_init_3737_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3752_, lean_object* v_elimTrivial_3753_, lean_object* v_n_3754_, lean_object* v_b_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
uint8_t v_elimTrivial_boxed_3761_; lean_object* v_res_3762_; 
v_elimTrivial_boxed_3761_ = lean_unbox(v_elimTrivial_3753_);
v_res_3762_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3752_, v_elimTrivial_boxed_3761_, v_n_3754_, v_b_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v_n_3754_);
lean_dec_ref(v_init_3752_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3763_, lean_object* v_t_3764_, lean_object* v_init_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_root_3771_; lean_object* v_tail_3772_; lean_object* v___x_3773_; 
v_root_3771_ = lean_ctor_get(v_t_3764_, 0);
v_tail_3772_ = lean_ctor_get(v_t_3764_, 1);
lean_inc_ref(v_init_3765_);
v___x_3773_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3765_, v_elimTrivial_3763_, v_root_3771_, v_init_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec_ref(v_init_3765_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3810_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3810_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3810_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
if (lean_obj_tag(v_a_3774_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; 
v_a_3778_ = lean_ctor_get(v_a_3774_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v_a_3774_, 1);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v_a_3778_);
v___x_3780_ = v___x_3776_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; size_t v_sz_3785_; size_t v___x_3786_; lean_object* v___x_3787_; 
lean_del_object(v___x_3776_);
v_a_3782_ = lean_ctor_get(v_a_3774_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v_a_3774_, 1);
v___x_3783_ = lean_box(0);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v_a_3782_);
v_sz_3785_ = lean_array_size(v_tail_3772_);
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3763_, v_tail_3772_, v_sz_3785_, v___x_3786_, v___x_3784_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3801_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3801_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3801_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_fst_3792_; 
v_fst_3792_ = lean_ctor_get(v_a_3788_, 0);
if (lean_obj_tag(v_fst_3792_) == 0)
{
lean_object* v_snd_3793_; lean_object* v___x_3795_; 
v_snd_3793_ = lean_ctor_get(v_a_3788_, 1);
lean_inc(v_snd_3793_);
lean_dec(v_a_3788_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_snd_3793_);
v___x_3795_ = v___x_3790_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_snd_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
else
{
lean_object* v_val_3797_; lean_object* v___x_3799_; 
lean_inc_ref(v_fst_3792_);
lean_dec(v_a_3788_);
v_val_3797_ = lean_ctor_get(v_fst_3792_, 0);
lean_inc(v_val_3797_);
lean_dec_ref_known(v_fst_3792_, 1);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_val_3797_);
v___x_3799_ = v___x_3790_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_val_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3787_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3787_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3773_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3773_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3819_, lean_object* v_t_3820_, lean_object* v_init_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v_elimTrivial_boxed_3827_; lean_object* v_res_3828_; 
v_elimTrivial_boxed_3827_ = lean_unbox(v_elimTrivial_3819_);
v_res_3828_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3827_, v_t_3820_, v_init_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec_ref(v_t_3820_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3829_, size_t v_sz_3830_, size_t v_i_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_usize_dec_lt(v_i_3831_, v_sz_3830_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v_b_3832_);
return v___x_3839_;
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_a_3840_ = lean_array_uget_borrowed(v_as_3829_, v_i_3831_);
v___x_3841_ = l_Lean_Expr_fvarId_x21(v_a_3840_);
v___x_3842_ = l_Lean_MVarId_tryClear(v_b_3832_, v___x_3841_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; size_t v___x_3844_; size_t v___x_3845_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = ((size_t)1ULL);
v___x_3845_ = lean_usize_add(v_i_3831_, v___x_3844_);
v_i_3831_ = v___x_3845_;
v_b_3832_ = v_a_3843_;
goto _start;
}
else
{
return v___x_3842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3847_, lean_object* v_sz_3848_, lean_object* v_i_3849_, lean_object* v_b_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
size_t v_sz_boxed_3856_; size_t v_i_boxed_3857_; lean_object* v_res_3858_; 
v_sz_boxed_3856_ = lean_unbox_usize(v_sz_3848_);
lean_dec(v_sz_3848_);
v_i_boxed_3857_ = lean_unbox_usize(v_i_3849_);
lean_dec(v_i_3849_);
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3847_, v_sz_boxed_3856_, v_i_boxed_3857_, v_b_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec_ref(v_as_3847_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3859_, lean_object* v_x_3860_, lean_object* v_x_3861_, lean_object* v_x_3862_){
_start:
{
lean_object* v_ks_3863_; lean_object* v_vs_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3888_; 
v_ks_3863_ = lean_ctor_get(v_x_3859_, 0);
v_vs_3864_ = lean_ctor_get(v_x_3859_, 1);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_x_3859_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3866_ = v_x_3859_;
v_isShared_3867_ = v_isSharedCheck_3888_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_vs_3864_);
lean_inc(v_ks_3863_);
lean_dec(v_x_3859_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3888_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3868_ = lean_array_get_size(v_ks_3863_);
v___x_3869_ = lean_nat_dec_lt(v_x_3860_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
lean_dec(v_x_3860_);
v___x_3870_ = lean_array_push(v_ks_3863_, v_x_3861_);
v___x_3871_ = lean_array_push(v_vs_3864_, v_x_3862_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 1, v___x_3871_);
lean_ctor_set(v___x_3866_, 0, v___x_3870_);
v___x_3873_ = v___x_3866_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
else
{
lean_object* v_k_x27_3875_; uint8_t v___x_3876_; 
v_k_x27_3875_ = lean_array_fget_borrowed(v_ks_3863_, v_x_3860_);
v___x_3876_ = l_Lean_instBEqMVarId_beq(v_x_3861_, v_k_x27_3875_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3878_; 
if (v_isShared_3867_ == 0)
{
v___x_3878_ = v___x_3866_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_ks_3863_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_vs_3864_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_unsigned_to_nat(1u);
v___x_3880_ = lean_nat_add(v_x_3860_, v___x_3879_);
lean_dec(v_x_3860_);
v_x_3859_ = v___x_3878_;
v_x_3860_ = v___x_3880_;
goto _start;
}
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3883_ = lean_array_fset(v_ks_3863_, v_x_3860_, v_x_3861_);
v___x_3884_ = lean_array_fset(v_vs_3864_, v_x_3860_, v_x_3862_);
lean_dec(v_x_3860_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 1, v___x_3884_);
lean_ctor_set(v___x_3866_, 0, v___x_3883_);
v___x_3886_ = v___x_3866_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3889_, lean_object* v_k_3890_, lean_object* v_v_3891_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3889_, v___x_3892_, v_k_3890_, v_v_3891_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3895_, size_t v_x_3896_, size_t v_x_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3895_) == 0)
{
lean_object* v_es_3900_; size_t v___x_3901_; size_t v___x_3902_; lean_object* v_j_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v_es_3900_ = lean_ctor_get(v_x_3895_, 0);
v___x_3901_ = ((size_t)31ULL);
v___x_3902_ = lean_usize_land(v_x_3896_, v___x_3901_);
v_j_3903_ = lean_usize_to_nat(v___x_3902_);
v___x_3904_ = lean_array_get_size(v_es_3900_);
v___x_3905_ = lean_nat_dec_lt(v_j_3903_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_dec(v_j_3903_);
lean_dec(v_x_3899_);
lean_dec(v_x_3898_);
return v_x_3895_;
}
else
{
lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3944_; 
lean_inc_ref(v_es_3900_);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_x_3895_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; 
v_unused_3945_ = lean_ctor_get(v_x_3895_, 0);
lean_dec(v_unused_3945_);
v___x_3907_ = v_x_3895_;
v_isShared_3908_ = v_isSharedCheck_3944_;
goto v_resetjp_3906_;
}
else
{
lean_dec(v_x_3895_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3944_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v_v_3909_; lean_object* v___x_3910_; lean_object* v_xs_x27_3911_; lean_object* v___y_3913_; 
v_v_3909_ = lean_array_fget(v_es_3900_, v_j_3903_);
v___x_3910_ = lean_box(0);
v_xs_x27_3911_ = lean_array_fset(v_es_3900_, v_j_3903_, v___x_3910_);
switch(lean_obj_tag(v_v_3909_))
{
case 0:
{
lean_object* v_key_3918_; lean_object* v_val_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3929_; 
v_key_3918_ = lean_ctor_get(v_v_3909_, 0);
v_val_3919_ = lean_ctor_get(v_v_3909_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_v_3909_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3921_ = v_v_3909_;
v_isShared_3922_ = v_isSharedCheck_3929_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_val_3919_);
lean_inc(v_key_3918_);
lean_dec(v_v_3909_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3929_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint8_t v___x_3923_; 
v___x_3923_ = l_Lean_instBEqMVarId_beq(v_x_3898_, v_key_3918_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_del_object(v___x_3921_);
v___x_3924_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3918_, v_val_3919_, v_x_3898_, v_x_3899_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
v___y_3913_ = v___x_3925_;
goto v___jp_3912_;
}
else
{
lean_object* v___x_3927_; 
lean_dec(v_val_3919_);
lean_dec(v_key_3918_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 1, v_x_3899_);
lean_ctor_set(v___x_3921_, 0, v_x_3898_);
v___x_3927_ = v___x_3921_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_x_3898_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_x_3899_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
v___y_3913_ = v___x_3927_;
goto v___jp_3912_;
}
}
}
}
case 1:
{
lean_object* v_node_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3942_; 
v_node_3930_ = lean_ctor_get(v_v_3909_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_v_3909_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3932_ = v_v_3909_;
v_isShared_3933_ = v_isSharedCheck_3942_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_node_3930_);
lean_dec(v_v_3909_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3942_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
size_t v___x_3934_; size_t v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3934_ = ((size_t)5ULL);
v___x_3935_ = lean_usize_shift_right(v_x_3896_, v___x_3934_);
v___x_3936_ = ((size_t)1ULL);
v___x_3937_ = lean_usize_add(v_x_3897_, v___x_3936_);
v___x_3938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3930_, v___x_3935_, v___x_3937_, v_x_3898_, v_x_3899_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3938_);
v___x_3940_ = v___x_3932_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
v___y_3913_ = v___x_3940_;
goto v___jp_3912_;
}
}
}
default: 
{
lean_object* v___x_3943_; 
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_x_3898_);
lean_ctor_set(v___x_3943_, 1, v_x_3899_);
v___y_3913_ = v___x_3943_;
goto v___jp_3912_;
}
}
v___jp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3914_ = lean_array_fset(v_xs_x27_3911_, v_j_3903_, v___y_3913_);
lean_dec(v_j_3903_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3914_);
v___x_3916_ = v___x_3907_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
else
{
lean_object* v_ks_3946_; lean_object* v_vs_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3965_; 
v_ks_3946_ = lean_ctor_get(v_x_3895_, 0);
v_vs_3947_ = lean_ctor_get(v_x_3895_, 1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_x_3895_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3949_ = v_x_3895_;
v_isShared_3950_ = v_isSharedCheck_3965_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_vs_3947_);
lean_inc(v_ks_3946_);
lean_dec(v_x_3895_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3965_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_ks_3946_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_vs_3947_);
v___x_3952_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v_newNode_3953_; size_t v___x_3954_; uint8_t v___x_3955_; 
v_newNode_3953_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3952_, v_x_3898_, v_x_3899_);
v___x_3954_ = ((size_t)7ULL);
v___x_3955_ = lean_usize_dec_le(v___x_3954_, v_x_3897_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3953_);
v___x_3957_ = lean_unsigned_to_nat(4u);
v___x_3958_ = lean_nat_dec_lt(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
if (v___x_3958_ == 0)
{
lean_object* v_ks_3959_; lean_object* v_vs_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_ks_3959_ = lean_ctor_get(v_newNode_3953_, 0);
lean_inc_ref(v_ks_3959_);
v_vs_3960_ = lean_ctor_get(v_newNode_3953_, 1);
lean_inc_ref(v_vs_3960_);
lean_dec_ref(v_newNode_3953_);
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3897_, v_ks_3959_, v_vs_3960_, v___x_3961_, v___x_3962_);
lean_dec_ref(v_vs_3960_);
lean_dec_ref(v_ks_3959_);
return v___x_3963_;
}
else
{
return v_newNode_3953_;
}
}
else
{
return v_newNode_3953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3966_, lean_object* v_keys_3967_, lean_object* v_vals_3968_, lean_object* v_i_3969_, lean_object* v_entries_3970_){
_start:
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3971_ = lean_array_get_size(v_keys_3967_);
v___x_3972_ = lean_nat_dec_lt(v_i_3969_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_dec(v_i_3969_);
return v_entries_3970_;
}
else
{
lean_object* v_k_3973_; lean_object* v_v_3974_; uint64_t v___x_3975_; size_t v_h_3976_; size_t v___x_3977_; lean_object* v___x_3978_; size_t v___x_3979_; size_t v___x_3980_; size_t v___x_3981_; size_t v_h_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_k_3973_ = lean_array_fget_borrowed(v_keys_3967_, v_i_3969_);
v_v_3974_ = lean_array_fget_borrowed(v_vals_3968_, v_i_3969_);
v___x_3975_ = l_Lean_instHashableMVarId_hash(v_k_3973_);
v_h_3976_ = lean_uint64_to_usize(v___x_3975_);
v___x_3977_ = ((size_t)5ULL);
v___x_3978_ = lean_unsigned_to_nat(1u);
v___x_3979_ = ((size_t)1ULL);
v___x_3980_ = lean_usize_sub(v_depth_3966_, v___x_3979_);
v___x_3981_ = lean_usize_mul(v___x_3977_, v___x_3980_);
v_h_3982_ = lean_usize_shift_right(v_h_3976_, v___x_3981_);
v___x_3983_ = lean_nat_add(v_i_3969_, v___x_3978_);
lean_dec(v_i_3969_);
lean_inc(v_v_3974_);
lean_inc(v_k_3973_);
v___x_3984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3970_, v_h_3982_, v_depth_3966_, v_k_3973_, v_v_3974_);
v_i_3969_ = v___x_3983_;
v_entries_3970_ = v___x_3984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3986_, lean_object* v_keys_3987_, lean_object* v_vals_3988_, lean_object* v_i_3989_, lean_object* v_entries_3990_){
_start:
{
size_t v_depth_boxed_3991_; lean_object* v_res_3992_; 
v_depth_boxed_3991_ = lean_unbox_usize(v_depth_3986_);
lean_dec(v_depth_3986_);
v_res_3992_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3991_, v_keys_3987_, v_vals_3988_, v_i_3989_, v_entries_3990_);
lean_dec_ref(v_vals_3988_);
lean_dec_ref(v_keys_3987_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_, lean_object* v_x_3997_){
_start:
{
size_t v_x_7826__boxed_3998_; size_t v_x_7827__boxed_3999_; lean_object* v_res_4000_; 
v_x_7826__boxed_3998_ = lean_unbox_usize(v_x_3994_);
lean_dec(v_x_3994_);
v_x_7827__boxed_3999_ = lean_unbox_usize(v_x_3995_);
lean_dec(v_x_3995_);
v_res_4000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3993_, v_x_7826__boxed_3998_, v_x_7827__boxed_3999_, v_x_3996_, v_x_3997_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4001_, lean_object* v_x_4002_, lean_object* v_x_4003_){
_start:
{
uint64_t v___x_4004_; size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v___x_4004_ = l_Lean_instHashableMVarId_hash(v_x_4002_);
v___x_4005_ = lean_uint64_to_usize(v___x_4004_);
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4001_, v___x_4005_, v___x_4006_, v_x_4002_, v_x_4003_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4008_, lean_object* v_val_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; lean_object* v_mctx_4013_; lean_object* v_cache_4014_; lean_object* v_zetaDeltaFVarIds_4015_; lean_object* v_postponed_4016_; lean_object* v_diag_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4047_; 
v___x_4012_ = lean_st_ref_take(v___y_4010_);
v_mctx_4013_ = lean_ctor_get(v___x_4012_, 0);
v_cache_4014_ = lean_ctor_get(v___x_4012_, 1);
v_zetaDeltaFVarIds_4015_ = lean_ctor_get(v___x_4012_, 2);
v_postponed_4016_ = lean_ctor_get(v___x_4012_, 3);
v_diag_4017_ = lean_ctor_get(v___x_4012_, 4);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4019_ = v___x_4012_;
v_isShared_4020_ = v_isSharedCheck_4047_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_diag_4017_);
lean_inc(v_postponed_4016_);
lean_inc(v_zetaDeltaFVarIds_4015_);
lean_inc(v_cache_4014_);
lean_inc(v_mctx_4013_);
lean_dec(v___x_4012_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4047_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v_depth_4021_; lean_object* v_levelAssignDepth_4022_; lean_object* v_lmvarCounter_4023_; lean_object* v_mvarCounter_4024_; lean_object* v_lDecls_4025_; lean_object* v_decls_4026_; lean_object* v_userNames_4027_; lean_object* v_lAssignment_4028_; lean_object* v_eAssignment_4029_; lean_object* v_dAssignment_4030_; lean_object* v_instanceTypedMVars_4031_; lean_object* v_synthNormMemo_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4046_; 
v_depth_4021_ = lean_ctor_get(v_mctx_4013_, 0);
v_levelAssignDepth_4022_ = lean_ctor_get(v_mctx_4013_, 1);
v_lmvarCounter_4023_ = lean_ctor_get(v_mctx_4013_, 2);
v_mvarCounter_4024_ = lean_ctor_get(v_mctx_4013_, 3);
v_lDecls_4025_ = lean_ctor_get(v_mctx_4013_, 4);
v_decls_4026_ = lean_ctor_get(v_mctx_4013_, 5);
v_userNames_4027_ = lean_ctor_get(v_mctx_4013_, 6);
v_lAssignment_4028_ = lean_ctor_get(v_mctx_4013_, 7);
v_eAssignment_4029_ = lean_ctor_get(v_mctx_4013_, 8);
v_dAssignment_4030_ = lean_ctor_get(v_mctx_4013_, 9);
v_instanceTypedMVars_4031_ = lean_ctor_get(v_mctx_4013_, 10);
v_synthNormMemo_4032_ = lean_ctor_get(v_mctx_4013_, 11);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_mctx_4013_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4034_ = v_mctx_4013_;
v_isShared_4035_ = v_isSharedCheck_4046_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_synthNormMemo_4032_);
lean_inc(v_instanceTypedMVars_4031_);
lean_inc(v_dAssignment_4030_);
lean_inc(v_eAssignment_4029_);
lean_inc(v_lAssignment_4028_);
lean_inc(v_userNames_4027_);
lean_inc(v_decls_4026_);
lean_inc(v_lDecls_4025_);
lean_inc(v_mvarCounter_4024_);
lean_inc(v_lmvarCounter_4023_);
lean_inc(v_levelAssignDepth_4022_);
lean_inc(v_depth_4021_);
lean_dec(v_mctx_4013_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4046_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4036_ = lean_box(0);
v___x_4037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4029_, v_mvarId_4008_, v_val_4009_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 8, v___x_4037_);
v___x_4039_ = v___x_4034_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_depth_4021_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_levelAssignDepth_4022_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_lmvarCounter_4023_);
lean_ctor_set(v_reuseFailAlloc_4045_, 3, v_mvarCounter_4024_);
lean_ctor_set(v_reuseFailAlloc_4045_, 4, v_lDecls_4025_);
lean_ctor_set(v_reuseFailAlloc_4045_, 5, v_decls_4026_);
lean_ctor_set(v_reuseFailAlloc_4045_, 6, v_userNames_4027_);
lean_ctor_set(v_reuseFailAlloc_4045_, 7, v_lAssignment_4028_);
lean_ctor_set(v_reuseFailAlloc_4045_, 8, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4045_, 9, v_dAssignment_4030_);
lean_ctor_set(v_reuseFailAlloc_4045_, 10, v_instanceTypedMVars_4031_);
lean_ctor_set(v_reuseFailAlloc_4045_, 11, v_synthNormMemo_4032_);
v___x_4039_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4041_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4039_);
v___x_4041_ = v___x_4019_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_cache_4014_);
lean_ctor_set(v_reuseFailAlloc_4044_, 2, v_zetaDeltaFVarIds_4015_);
lean_ctor_set(v_reuseFailAlloc_4044_, 3, v_postponed_4016_);
lean_ctor_set(v_reuseFailAlloc_4044_, 4, v_diag_4017_);
v___x_4041_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_st_ref_put(v___y_4010_, v___x_4041_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4036_);
return v___x_4043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4048_, lean_object* v_val_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4048_, v_val_4049_, v___y_4050_);
lean_dec(v___y_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4055_, uint8_t v_elimTrivial_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_lctx_4062_; lean_object* v___x_4063_; 
v_lctx_4062_ = lean_ctor_get(v___y_4057_, 2);
lean_inc(v_mvar_4055_);
v___x_4063_ = l_Lean_MVarId_getType(v_mvar_4055_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4066_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4064_, v___x_4065_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v_fst_4068_; lean_object* v_snd_4069_; lean_object* v___x_4070_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v_fst_4068_ = lean_ctor_get(v_a_4067_, 0);
lean_inc(v_fst_4068_);
v_snd_4069_ = lean_ctor_get(v_a_4067_, 1);
lean_inc(v_snd_4069_);
lean_dec(v_a_4067_);
lean_inc_ref(v_lctx_4062_);
v___x_4070_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4062_, v_snd_4069_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; lean_object* v_decls_4073_; lean_object* v___x_4074_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4073_ = lean_ctor_get(v_a_4071_, 1);
lean_inc_ref(v_decls_4073_);
lean_dec(v_a_4071_);
v___x_4074_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4056_, v_decls_4073_, v___x_4072_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec_ref(v_decls_4073_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v_fst_4076_; lean_object* v_snd_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v_fst_4076_ = lean_ctor_get(v_a_4075_, 0);
lean_inc(v_fst_4076_);
v_snd_4077_ = lean_ctor_get(v_a_4075_, 1);
lean_inc(v_snd_4077_);
lean_dec(v_a_4075_);
v___x_4078_ = l_Lean_Expr_replaceFVars(v_fst_4068_, v_fst_4076_, v_snd_4077_);
lean_dec(v_snd_4077_);
lean_dec(v_fst_4068_);
v___x_4079_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4078_, v_elimTrivial_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
lean_inc(v_mvar_4055_);
v___x_4081_ = l_Lean_MVarId_getTag(v_mvar_4055_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v___x_4083_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4080_, v_a_4082_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; size_t v_sz_4087_; size_t v___x_4088_; lean_object* v___x_4089_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_n(v_a_4084_, 2);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4055_, v_a_4084_, v___y_4058_);
lean_dec_ref(v___x_4085_);
v___x_4086_ = l_Lean_Expr_mvarId_x21(v_a_4084_);
lean_dec(v_a_4084_);
v_sz_4087_ = lean_array_size(v_fst_4076_);
v___x_4088_ = ((size_t)0ULL);
v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4076_, v_sz_4087_, v___x_4088_, v___x_4086_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec_ref(v___y_4057_);
lean_dec(v_fst_4076_);
return v___x_4089_;
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_fst_4076_);
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4090_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4083_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4083_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_a_4080_);
lean_dec(v_fst_4076_);
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4098_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4081_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4081_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_fst_4076_);
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4106_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4079_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4079_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4114_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4074_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4074_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4122_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4070_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4070_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4130_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4066_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4066_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v___y_4057_);
lean_dec(v_mvar_4055_);
v_a_4138_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4063_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4063_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4146_, lean_object* v_elimTrivial_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
uint8_t v_elimTrivial_boxed_4153_; lean_object* v_res_4154_; 
v_elimTrivial_boxed_4153_ = lean_unbox(v_elimTrivial_4147_);
v_res_4154_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4146_, v_elimTrivial_boxed_4153_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4155_, uint8_t v_elimTrivial_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v___x_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; 
v___x_4162_ = lean_box(v_elimTrivial_4156_);
lean_inc(v_mvar_4155_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4163_, 0, v_mvar_4155_);
lean_closure_set(v___f_4163_, 1, v___x_4162_);
v___x_4164_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4155_, v___f_4163_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4165_, lean_object* v_elimTrivial_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
uint8_t v_elimTrivial_boxed_4172_; lean_object* v_res_4173_; 
v_elimTrivial_boxed_4172_ = lean_unbox(v_elimTrivial_4166_);
v_res_4173_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4165_, v_elimTrivial_boxed_4172_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4174_, lean_object* v_val_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4174_, v_val_4175_, v___y_4177_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4182_, lean_object* v_val_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4182_, v_val_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4190_, lean_object* v_x_4191_, lean_object* v_x_4192_, lean_object* v_x_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4191_, v_x_4192_, v_x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4195_, lean_object* v_as_4196_, size_t v_sz_4197_, size_t v_i_4198_, lean_object* v_b_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4195_, v_as_4196_, v_sz_4197_, v_i_4198_, v_b_4199_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4206_, lean_object* v_as_4207_, lean_object* v_sz_4208_, lean_object* v_i_4209_, lean_object* v_b_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v_elimTrivial_boxed_4216_; size_t v_sz_boxed_4217_; size_t v_i_boxed_4218_; lean_object* v_res_4219_; 
v_elimTrivial_boxed_4216_ = lean_unbox(v_elimTrivial_4206_);
v_sz_boxed_4217_ = lean_unbox_usize(v_sz_4208_);
lean_dec(v_sz_4208_);
v_i_boxed_4218_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4216_, v_as_4207_, v_sz_boxed_4217_, v_i_boxed_4218_, v_b_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_as_4207_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4220_, lean_object* v_x_4221_, size_t v_x_4222_, size_t v_x_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4221_, v_x_4222_, v_x_4223_, v_x_4224_, v_x_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4227_, lean_object* v_x_4228_, lean_object* v_x_4229_, lean_object* v_x_4230_, lean_object* v_x_4231_, lean_object* v_x_4232_){
_start:
{
size_t v_x_8272__boxed_4233_; size_t v_x_8273__boxed_4234_; lean_object* v_res_4235_; 
v_x_8272__boxed_4233_ = lean_unbox_usize(v_x_4229_);
lean_dec(v_x_4229_);
v_x_8273__boxed_4234_ = lean_unbox_usize(v_x_4230_);
lean_dec(v_x_4230_);
v_res_4235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4227_, v_x_4228_, v_x_8272__boxed_4233_, v_x_8273__boxed_4234_, v_x_4231_, v_x_4232_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4236_, lean_object* v_as_4237_, size_t v_sz_4238_, size_t v_i_4239_, lean_object* v_b_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4236_, v_as_4237_, v_sz_4238_, v_i_4239_, v_b_4240_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4247_, lean_object* v_as_4248_, lean_object* v_sz_4249_, lean_object* v_i_4250_, lean_object* v_b_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
uint8_t v_elimTrivial_boxed_4257_; size_t v_sz_boxed_4258_; size_t v_i_boxed_4259_; lean_object* v_res_4260_; 
v_elimTrivial_boxed_4257_ = lean_unbox(v_elimTrivial_4247_);
v_sz_boxed_4258_ = lean_unbox_usize(v_sz_4249_);
lean_dec(v_sz_4249_);
v_i_boxed_4259_ = lean_unbox_usize(v_i_4250_);
lean_dec(v_i_4250_);
v_res_4260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4257_, v_as_4248_, v_sz_boxed_4258_, v_i_boxed_4259_, v_b_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec_ref(v_as_4248_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4261_, lean_object* v_n_4262_, lean_object* v_k_4263_, lean_object* v_v_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4262_, v_k_4263_, v_v_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4266_, size_t v_depth_4267_, lean_object* v_keys_4268_, lean_object* v_vals_4269_, lean_object* v_heq_4270_, lean_object* v_i_4271_, lean_object* v_entries_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4267_, v_keys_4268_, v_vals_4269_, v_i_4271_, v_entries_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4274_, lean_object* v_depth_4275_, lean_object* v_keys_4276_, lean_object* v_vals_4277_, lean_object* v_heq_4278_, lean_object* v_i_4279_, lean_object* v_entries_4280_){
_start:
{
size_t v_depth_boxed_4281_; lean_object* v_res_4282_; 
v_depth_boxed_4281_ = lean_unbox_usize(v_depth_4275_);
lean_dec(v_depth_4275_);
v_res_4282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4274_, v_depth_boxed_4281_, v_keys_4276_, v_vals_4277_, v_heq_4278_, v_i_4279_, v_entries_4280_);
lean_dec_ref(v_vals_4277_);
lean_dec_ref(v_keys_4276_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4283_, lean_object* v_x_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_, lean_object* v_x_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4284_, v_x_4285_, v_x_4286_, v_x_4287_);
return v___x_4288_;
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
